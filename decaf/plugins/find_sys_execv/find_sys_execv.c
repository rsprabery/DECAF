#include "DECAF_types.h"
#include "DECAF_main.h"
#include "DECAF_callback.h"
#include "DECAF_target.h"
#include "DECAF_callback_common.h"
#include "utils/Output.h"
#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <inttypes.h>
#include <xed-interface.h>
#include <time.h>
#include <pthread.h>

/*
 * Quick and dirty plugin to locate the scheduler function and 
 * also bound it to determine a maximum detection latency
 */


xed_uint_t insn_len;
#define MAX_INSN_BYTES 15 /* Maximum number of bytes in a x86 instruction */

static plugin_interface_t my_interface;
static DECAF_Handle vmcall_handle = DECAF_NULL_HANDLE;
static DECAF_Handle insn_end_handle = DECAF_NULL_HANDLE;
static char trace_filename[128];
static FILE *tracefile;
static uint count;

static unsigned last_sched;
static int get_next_instr;

static int found_sched_times; //by "times" I meant "count"
int found_sched; //boolean when we've found it
struct timeval last_sched_time, largest_deltat;

static time_t start_time = NULL;

static unsigned find_function_header(CPUState *env, unsigned gva) {
    int i;
    int SEARCH_LEN = 4096;
    uint8_t insns[SEARCH_LEN];

    DECAF_read_mem(env, (gva - SEARCH_LEN), SEARCH_LEN, insns);
    //Search backwards until we find a function protoype
    for (i = SEARCH_LEN - 1; i > 1; i--) {
        //push ebp; mov esp,ebp
        //55 89 e5
        if (insns[i] == 0xe5 && insns[i - 1] == 0x89 && insns[i - 2] == 0x55) {
            fprintf(tracefile, "i: %d insns: %x\n", i,
                    (int) (insns[i] | ((int) insns[i - 1] << 8) | ((int) insns[i - 2] << 16)));
            return gva - SEARCH_LEN + i - 2;
        }
    }
    return 0;
}

//copied from
//http://www.gnu.org/software/libc/manual/html_node/Elapsed-Time.html

static int timeval_subtract(struct timeval *result, struct timeval *x, struct timeval *y) {
    /* Perform the carry for the later subtraction by updating y. */
    if (x->tv_usec < y->tv_usec) {
        int nsec = (y->tv_usec - x->tv_usec) / 1000000 + 1;
        y->tv_usec -= 1000000 * nsec;
        y->tv_sec += nsec;
    }
    if (x->tv_usec - y->tv_usec > 1000000) {
        int nsec = (x->tv_usec - y->tv_usec) / 1000000;
        y->tv_usec += 1000000 * nsec;
        y->tv_sec -= nsec;
    }

    /* Compute the time remaining to wait.
     *      tv_usec is certainly positive. */
    result->tv_sec = x->tv_sec - y->tv_sec;
    result->tv_usec = x->tv_usec - y->tv_usec;

    /* Return 1 if result is negative. */
    return x->tv_sec < y->tv_sec;
}

typedef enum FUNCTION_FIND_STATES {
    FOUND_NOTHING,
    FOUND_PUSH
} FunctionState;

static FunctionState currentFunctionFindState = FOUND_NOTHING;
static const int NUM_FUNCTION_TO_TRACK = 10;
static target_ulong function_call_array[10];
static target_ulong temp_address_tracking = 0;

static void init_function_call_array() {
    int i = 0;
    for (i = 0; i < NUM_FUNCTION_TO_TRACK; i++) {
        function_call_array[i] = 0;
    }
}
static int keep_adding_elements = 1;

static void insert_and_rotate(target_ulong value) {
    int i = 0;
    int temp = 0;
    for (i = NUM_FUNCTION_TO_TRACK - 1; i >= 0; i--) {
        if (i == NUM_FUNCTION_TO_TRACK - 1)
            temp = function_call_array[i];

        if (i != 0)
            function_call_array[i] = function_call_array[i - 1];
        else
            function_call_array[0] = value;
    }

}

//static int print_counter = 0;

static void find_function_calls(CPUState *env) {
    //    print_counter++;
    //    pthread_t self = pthread_self();
    //    if (print_counter % 10000 == 0) {
    //        DECAF_printf("Thread id: %x\n", self);
    //    }
    //    //DECAF_printf("finding function call\n");
    unsigned char insn[MAX_INSN_BYTES];
    DECAF_read_mem(env, env->eip, MAX_INSN_BYTES, insn);
    //DECAF_printf("got memory for the instruction\n");
    switch (currentFunctionFindState) {
        case FOUND_NOTHING:
        {
            //DECAF_printf("in the found nothign state\n");
            //looking for push %ebp (0x55)
            if (insn[0] == 0x55) {
                temp_address_tracking = env->eip;
                currentFunctionFindState = FOUND_PUSH;
            }
            break;
        }
        case FOUND_PUSH:
        {
            //DECAF_printf("in the found push state\n");
            // looking for mov %esp, %ebp (0x89, 0xe5)
            if (insn[0] == 0x89 && insn[1] == 0xe5) {
                // Store the address of the found PUSH (function start address))
                insert_and_rotate(temp_address_tracking);
            }

            // Regardless of the finding "mov" we'll need to wait for another
            // push.
            temp_address_tracking = 0;
            currentFunctionFindState = FOUND_NOTHING;
            break;
        };
    }
}

static void print_function_addresses(FILE *tracefile) {
    fprintf(tracefile, "Addresses called before last instruction: \n");
    int i = 0;

    for (i = 0; i < NUM_FUNCTION_TO_TRACK; i++) {
        target_ulong value = function_call_array[i];
        fprintf(tracefile, "%x\n", value);
    }
    fprintf(tracefile, "-----------------------------------------------\n");
}

#define FIND_SCHED_THRES 5 

time_t last_cr3_write = NULL;
int foundAnInterrupt = 0;
int instructionsBetweenFlush = 0;
int foundSysExecInterrupt = 0;
int addressOfGeneralInterruptHandler = 0;
int callAfterInterruptFound = 0;
int addressOfFunctionCalled = 0;
int previousEip = 0;

static void insn_end_callback(DECAF_Callback_Params* params) {
    unsigned char insn[MAX_INSN_BYTES];

    unsigned bytes;
    xed_decoded_inst_t insn_decoded;

    CPUState* env = NULL;
    if (!params) return;
    env = params->ie.env;
    if (!env) {
        DECAF_printf("env is NULL!\n");
        return;
    }

    DECAF_read_mem(env, env->eip, MAX_INSN_BYTES, insn);

    xed_decoded_inst_zero(&insn_decoded);
    xed_decoded_inst_set_mode(&insn_decoded, XED_MACHINE_MODE_LEGACY_32,
            XED_ADDRESS_WIDTH_32b);
    xed_decode(&insn_decoded, (const xed_uint8_t *) insn, MAX_INSN_BYTES);
    insn_len = xed_decoded_inst_get_length(&insn_decoded);
    insn_len = insn_len > MAX_INSN_BYTES ? MAX_INSN_BYTES : insn_len;
    
    if ((insn[0] == 0xcd && insn[1] == 0x80) && env->regs[R_EAX] == 11 && foundSysExecInterrupt == 0 && addressOfGeneralInterruptHandler == 0) { 
        foundSysExecInterrupt = 1;
        fprintf(tracefile, "Found Linux System Exec Interrupt Call!\n");
//        if (foundAnInterrupt) {
//            fprintf(tracefile, "An interrupt was called again before a cr3 write was called!\n");
//            fprintf(tracefile, "Instruction count in kernel since previous interrupt: %u\n", count);
//            fprintf(tracefile, "Resetting count now!\n");
//            count = 0;
//        }
//        
//        fprintf(tracefile, "FOUND INT Call at: %x\n", env->eip);
//        int eax_sys_call_num = env->regs[R_EAX];
//        fprintf(tracefile, "EAX register (sys call #): %u\n", eax_sys_call_num);
//        
//        foundAnInterrupt = 1;
    } else if (foundSysExecInterrupt) {
        foundSysExecInterrupt = 0;
        addressOfGeneralInterruptHandler = env->eip;
        fprintf(tracefile, "General Interrupt Handler at 0x%x\n", addressOfGeneralInterruptHandler);
    } else if (addressOfGeneralInterruptHandler != 0) {
        if (env->eip > addressOfGeneralInterruptHandler && env->eip < addressOfGeneralInterruptHandler + 100) {
            //TODO: This part would likely be much better with XED
            
            if (insn[0] == 0x9a) { // absolute call
                fprintf(tracefile, "Absolute call!\n");
                callAfterInterruptFound = 0;
                previousEip = env->eip;
                addressOfFunctionCalled = insn[1]; // offset is the only arg to call 
                addressOfGeneralInterruptHandler = 0;
            } else if (insn[0] == 0xe8) { //relative call
                fprintf(tracefile, "relative call!\n");
                addressOfGeneralInterruptHandler = 0;
            } else if (insn[0] == 0xff) {
                fprintf(tracefile, "some other call!\n");
                addressOfGeneralInterruptHandler = 0;
            }
        }
    }

//    if (foundAnInterrupt) {
//        if (DECAF_is_in_kernel(env)) {
//            count++;
//            /*check for write to cr3
//            for movcr, mod=11 (register direct)
//            so move to cr3 would always have 1101 1XXX & d8 == 1*/
//            if (insn[0] == 0x0f && insn[1] == 0x22 && ((insn[2] & 0xf8) == 0xd8)) {
//                fprintf(tracefile, "CR3 Write at: %x\n", env->eip);
//                fprintf(tracefile, "Instruction count in kernel between interrupt and CR3 write: %u\n", count);
//                fprintf(tracefile, "Resetting count and found interrupt flag!\n");
//                count = 0;
//                foundAnInterrupt = 0;
//                return;
//            }
//        }
//    }
    
    //fflush(tracefile);
    if (instructionsBetweenFlush >= 500000) {
        fflush(tracefile);
        instructionsBetweenFlush = 0;
    }
    
    instructionsBetweenFlush++;
}

static void stop_tracing(void) {
    DECAF_stop_vm();
    if (insn_end_handle != DECAF_NULL_HANDLE) {
        DECAF_unregister_callback(DECAF_INSN_END_CB, insn_end_handle);
        insn_end_handle = DECAF_NULL_HANDLE;
    }

    if (tracefile != NULL) {
        fclose(tracefile);
        tracefile = NULL;
    }
    DECAF_start_vm();
}

static void my_cleanup(void) {
    stop_tracing();
    if (vmcall_handle != DECAF_NULL_HANDLE) {
        DECAF_unregister_callback(DECAF_VMCALL_CB, vmcall_handle);
        vmcall_handle = DECAF_NULL_HANDLE;
    }
}

static void start_tracing(void) {
    DECAF_stop_vm();
    get_next_instr = 0;
    found_sched_times = 0;
    found_sched = 0;
    count = 0;
    instructionsBetweenFlush = 0;
    foundSysExecInterrupt = 0;
    addressOfGeneralInterruptHandler = 0;
    callAfterInterruptFound = 0;
    addressOfFunctionCalled = 0;
    foundAnInterrupt = 0;
    largest_deltat.tv_sec = 0;
    largest_deltat.tv_usec = 0;
    /* start instruction tracing and initiliaze variables */
    if (trace_filename[0] == '\0') {
        DECAF_printf("Set filename first using command!\n");
        return;
    }

    tracefile = fopen(trace_filename, "w");
    if (tracefile == NULL) {
        DECAF_printf("Couldn't open file %s: %s", trace_filename,
                strerror(errno));
        return;
    }
    DECAF_printf("writing output to %s\n", trace_filename);
    insn_end_handle = DECAF_register_callback(DECAF_INSN_END_CB,
            insn_end_callback, NULL);
    DECAF_start_vm();
}

static void vmcall_callback(DECAF_Callback_Params * params) {
    int callnum;
    if (!params)
        return;
    callnum = params->ie.env->regs[R_EAX];

    DECAF_printf("Got vmcall number %x!\n", callnum);
    if (callnum == 0) {
        start_tracing();
    } else {
        /* stop instruction tracing */
        stop_tracing();
    }
}

void set_filename(Monitor *mon, const QDict * qdict) {
    const char* filename_str = qdict_get_str(qdict, "filepath");
    strncpy(trace_filename, filename_str, 128);
    DECAF_printf("set trace file to %s\n", trace_filename);
}

static mon_cmd_t my_term_cmds[] = {
    {
        .name = "set_filename",
        .args_type = "filepath:F",
        .mhandler.cmd = set_filename,
        .params = "filepath",
        .help = "start kernel trace on vmcall 0, stop on 1, saving into the specified file"
    },
    {
        .name = "stop_tracing",
        .args_type = "",
        .mhandler.info = stop_tracing,
        .params = "",
        .help = "stop tracing"
    },
    {
        .name = "start_tracing",
        .args_type = "",
        .mhandler.info = start_tracing,
        .params = "",
        .help = "start tracing"
    },
    {NULL, NULL,},
};

plugin_interface_t * init_plugin(void) {
    xed_tables_init();
    my_interface.mon_cmds = my_term_cmds;
    my_interface.plugin_cleanup = &my_cleanup;

    trace_filename[0] = '\0';
    tracefile = NULL;

    vmcall_handle = DECAF_register_callback(DECAF_VMCALL_CB, &vmcall_callback,
            NULL);
    if (vmcall_handle == DECAF_NULL_HANDLE) {
        DECAF_printf("Could not register for the vmcall_CB\n");
    }
    init_function_call_array();
    start_time = time(NULL);
    return (&my_interface);
}
