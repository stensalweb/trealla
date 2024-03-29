#!/bin/sh

# set -e

TPL=./tpl

TMP=tmp.out

trap "rm -f $TMP" EXIT

failed_count=0
succeeded_count=0

for source in tests/tests/*
do
	case "$source" in
		*.pro)
			cmd="$TPL -q -l "
			;;
		*.sh)
			cmd="env TPL=$TPL sh"
			;;
		*)
			continue
	esac

	echo "Running $source ..."
	$cmd "$source" >$TMP
	diff "${source%.*}.expected" $TMP
	if [ $? -eq 0 ]
	then
		succeeded_count=$(expr $succeeded_count + 1)
	else
		failed_count=$(expr $failed_count + 1)
	fi
done

cat <<EOF

============
TEST SUMMARY
============
Failed: $failed_count
Succeeded: $succeeded_count
EOF
