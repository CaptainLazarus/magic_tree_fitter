grammar test;

s
    : a+ b+ EOF
    ;

a
    : A a
    ;

b
    : B b
    ;
