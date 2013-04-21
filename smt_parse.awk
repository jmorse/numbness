#!/usr/bin/awk -f
# Simplified approach: only pick out lines with round definitions
/^\(\(round.*\)\)$/ {
	print $0;
}
