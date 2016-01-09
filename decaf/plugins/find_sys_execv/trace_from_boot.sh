#!/bin/bash

# $1 = filename
# $2 = socket

#I start my qemu (from decaf/) with these arguments:
# /home/read/workspace/DECAF/decaf/i386-softmmu/qemu-system-i386 -m 2048 -netdev user,id=mynet0 -device rtl8139,netdev=mynet0 -nographic -redir tcp:11022::22 -chardev socket,id=monitor,path=./fedora9_monitor.sock,server,nowait -monitor chardev:monitor /media/sdc1/sprabery_scratch/fedora9.img.fs 

SOCKET=$2

#Run a command in the qemu monitor
mon_cmd() {
  echo $1 | nc -U $SOCKET
}

echo "Timestamp after VM boot" >> $1
echo `date +%s` >> $1
mon_cmd 'unload_plugin'
mon_cmd "load_plugin `pwd`/find_sys_execv.so"
mon_cmd "set_filename ${1}"
mon_cmd "start_tracing"
