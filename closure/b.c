/* A function of two argyments that we want to apply partially.  */
static int
add (int a, int b)
{
    return a + b;
}

static int
sub (int a, int b)
{
    return a - b;
}

static int
inc (int x)
{
    return x + 1;
}


/* A type for partial application over one argument.  */
struct add_1_t
{
    int x;
    int (*f) (int, int);
};


/* A function to create a partial application.  */
static struct add_1_t
mk_partial_adder (int x)
{
    return (struct add_1_t){.x = x, .f = &add};
}


/* Use partial application as one-argument function.  */
static int
apply_add_1_t (struct add_1_t func, int y)
{
    return func.f (func.x, y);
}




enum kind_int_to_int {
    k_native,
    k_partial_int_int,
    k_partial_float_int,
};


struct int_to_int_base {
    enum kind_int_to_int kind;
};

struct int_to_int_native {
    enum kind_int_to_int kind;
    int (*f) (int);
};

struct int_to_int_partial_int_int {
    enum kind_int_to_int kind;
    int arg1;
    int (*f) (int, int);
};

struct int_to_int_partial_float_int {
    enum kind_int_to_int kind;
    float arg1;
    int (*f) (float, int);
};

union int_to_int {
    struct int_to_int_base base;
    struct int_to_int_native native;
    struct int_to_int_partial_int_int partial_int_int;
    struct int_to_int_partial_float_int partial_float_int;
};


static int
apply_int_to_int (union int_to_int f, int x) {
    switch (f.base.kind) {
    case k_native:
        return f.native.f (x);
    case k_partial_int_int:
        return f.partial_int_int.f (f.partial_int_int.arg1, x);
    case k_partial_float_int:
        return f.partial_float_int.f (f.partial_float_int.arg1, x);
    }
}



static int
foo (union int_to_int f, int x)
{
    return apply_int_to_int (f, x+1);
}




int main (int argc, char *argv[])
{
    struct int_to_int_partial_int_int cl = {.kind = k_partial_int_int,
                                            .arg1 = 3,
                                            .f = add };
    struct int_to_int_native cl_inc = {.kind = k_native,
                                       .f = inc };

    return argc > 1 ? foo ((union int_to_int)cl, argc)
                    : foo ((union int_to_int)cl_inc, argc);

}
