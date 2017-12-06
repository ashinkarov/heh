enum type_kind {
    k_int,
    k_float,
    k_fun
};

union type;

struct type_base {
    enum type_kind kind;
};

struct type_fun {
    enum type_kind kind;
    union type *arg;
    union type *ret;
};

union type {
    struct type_base base;
    struct type_fun fun;
};



struct closure {
    int arg_len;
    union type *env;
    void *code;
};


int add (int x, int y)
{
    return x + y;
}

struct closure add_cl = {
    .arg_len = 2,
    .env = [(union type)(struct type_base){k_int}, (union type)(struct type_base){k_int}],
    .code = (void *)add
};
