#!/usr/bin/awk -f

BEGIN{
	outarr[0] = "";
	outarr[1] = "";
	outarr[2] = "";
	outarr[3] = "";
	idx = 0;
}

/.*sparticus.*/{
	sub(/bv/, "", $12);
	outarr[idx] = $12;
	idx++;
	if (idx == 4) {
		print outarr[0] "|" outarr[1] "|" outarr[2] "|" outarr[3]
		idx = 0;
	}
}
