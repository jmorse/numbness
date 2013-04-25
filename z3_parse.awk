#!/usr/bin/awk -f

BEGIN{
	outarr[0] = "";
	outarr[1] = "";
	outarr[2] = "";
	outarr[3] = "";
	idx = 0;
}

/.*sparticus.*/{
	sub(/#b/, "", $11);
	sub(/))/, "", $11);
	cmd = "echo \"obase=10\nibase=2\n" $11 "\" | bc";
	cmd |getline output;
	close(cmd);
	outarr[idx] = output;
	idx++;
	if (idx == 4) {
		print outarr[0] "|" outarr[1] "|" outarr[2] "|" outarr[3]
		idx = 0;
	}
}
