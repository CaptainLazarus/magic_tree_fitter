grammar test;

s
    : np vp EOF
    ;

np
    : N
    ;

np
    : np pp
    ;

vp
    : V np
    ;

pp
	: P np
	;
