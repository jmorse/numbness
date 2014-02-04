from config import *

def print_integer(val, width):
        return "(_ bv{0} {1})".format(val, width)

def sparticus(r, match, slot):
        return "(sparticus {0} {1} {2})".format(print_integer(r, ROUNDBITS),
                        print_integer(match, MATCHBITS),
                        print_integer(slot, SLOTBITS))

def read_smt_bvnum(num):
	lparen, underscore, bvnum, width, rparen = num
	bvnum, = bvnum
	bvnum = bvnum[2:]
	return int(bvnum)

def read_func_app(expr):
	# Function application looks like this:
	# (sparticus (_ bv0 4) (_ bv0 4) (_ bv0 2))
	# And we can be confident that it has the righ tnumber of vars.
	lparen, funcname, arg1, arg2, arg3, rparen = expr
	return read_smt_bvnum(arg1), read_smt_bvnum(arg2), read_smt_bvnum(arg3)

def read_assign(string):
	if len(string) == 1:
		string, = string
		hash, bee, string2 = string
		if hash == '#' and bee == 'b':
			return int(string2, 2)
		else:
			raise Exception("I don't recognize SMT string {0}".format(string))
	else:
		return read_smt_bvnum(string)
