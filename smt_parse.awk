#!/usr/bin/gawk -f
# Simplified approach: only pick out lines with round definitions
/^\(\(round.*\)\)$/ {
	print $0;
}
