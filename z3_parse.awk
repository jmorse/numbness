#!/usr/bin/gawk -f
BEGIN{
	bees="";
}

/^[ ]+\(define-fun.*round.*Int$/{
	bees = $2;
}

/^[ ]+[0-9]+\)$/{
	match ($0, /^[ ]+([0-9]+)\)/, arr)
	print bees " " arr[1];
}
