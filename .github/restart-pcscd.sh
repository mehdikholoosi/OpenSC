#!/bin/bash -e

# This file is made to be sourced into other test scripts and not executed
# manually because it sets trap to restore pcscd to working state

# register cleanup handler
function pcscd_cleanup {
	echo "Process terminated: resetting pcscd"
	sudo pkill pcscd
	sudo systemctl start pcscd.socket
}
trap pcscd_cleanup EXIT


# stop the pcscd service and run it from console to see possible errors
sudo systemctl stop pcscd.service pcscd.socket
sudo /usr/sbin/pcscd -f | sed -e 's/^/pcscd: /;' &


# Try to wait up to 30 seconds for pcscd to come up and create PID file
for ((i=1;i<=30;i++)); do
	echo "Waiting for pcscd to start: $i s"
	if [ -f "/var/run/pcscd/pcscd.pid" ]; then
		break
	fi
	sleep 1
done


# if it did not come up, warn, but continue
if [ ! -f "/var/run/pcscd/pcscd.pid" ]; then
	echo "WARNING: The pcscd pid file does not exist ... trying anyway"
fi