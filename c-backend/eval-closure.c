#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdbool.h>


enum value_kind {
    k_scalar,
    k_evaluated_array,
    k_array_closure
};

typedef union value_union value;

// A type for the inner imap function.
typedef value (*imap_fun) (value);

struct scalar_value {
    enum value_kind kind;
    int val;
};

struct evaluated_array {
    enum value_kind kind;
    size_t size;
    int *val;
};

struct array_closure {
    enum value_kind kind;
    size_t size;
    int *val;
    bool *mask;
    imap_fun f;
};

union value_union {
    enum value_kind val_kind;
    struct scalar_value val_scal;
    struct evaluated_array val_evarr;
    struct array_closure val_clarr;
};


// helper functions
void
value_print (value v)
{
    switch (v.val_kind) {
    case k_scalar:
        printf ("scalar[%d]", v.val_scal.val);
        break;
    case k_evaluated_array:
        printf ("ev_array[");
        for (size_t i = 0; i < v.val_evarr.size; i++) {
            printf ("%d, ", v.val_evarr.val[i]);
        }
        printf ("]");
        break;
    case k_array_closure:
        printf ("array_closure (f=%p, [", v.val_clarr.f);
        for (size_t i = 0; i < v.val_clarr.size; i++) {
            if (v.val_clarr.mask[i])
                printf ("[%zu]=%d, ", i, v.val_clarr.val[i]);
        }
        printf ("])");
        break;
    default:
        abort ();
    }
}

// mk helper functions
value
mk_evaluated_array (size_t size)
{
    struct evaluated_array ea;
    ea.kind = k_evaluated_array;
    ea.size = size;
    ea.val = malloc (sizeof (int) * size);
    return (value)ea;
}

value
mk_array_closure (size_t size, imap_fun f)
{
    struct array_closure ac;
    ac.kind = k_array_closure;
    ac.size = size;
    ac.val = malloc (sizeof (int) * size);
    ac.mask = malloc (sizeof (bool) * size);
    // All the mask elements are false.
    memset (ac.mask, 0, sizeof (bool) * size);
    ac.f = f;
    return (value)ac;
}

value
mk_scalar (int val)
{
    struct scalar_value v;
    v.kind = k_scalar;
    v.val = val;
    return (value)v;
}


value
eval_imap (size_t size, imap_fun f)
{
    struct evaluated_array v = mk_evaluated_array (size).val_evarr;

    for (size_t i = 0; i < size; i++) {
        value vi = f (mk_scalar (i));
        assert (vi.val_kind == k_scalar);
        v.val[i] = vi.val_scal.val;
    }

    return (value)v;
}

value
eval_imap_closure (size_t size, imap_fun f)
{
    return mk_array_closure (size, f);
}

value
eval_eq (value l, value r)
{
    assert (l.val_kind == k_scalar);
    assert (r.val_kind == k_scalar);
    //printf ("cmp %d == %d\n", l->val_scal.val, r->val_scal.val);
    return mk_scalar (l.val_scal.val == r.val_scal.val);
}

value
eval_plus (value l, value r)
{
    assert (l.val_kind == k_scalar);
    assert (r.val_kind == k_scalar);
    return mk_scalar (l.val_scal.val + r.val_scal.val);
}

value
eval_minus (value l, value r)
{
    assert (l.val_kind == k_scalar);
    assert (r.val_kind == k_scalar);
    return mk_scalar (l.val_scal.val - r.val_scal.val);
}

value
eval_div (value l, value r)
{
    assert (l.val_kind == k_scalar);
    assert (r.val_kind == k_scalar);
    return mk_scalar (l.val_scal.val / r.val_scal.val);
}

value
eval_sel (value a, value idx)
{
    assert (a.val_kind == k_evaluated_array || a.val_kind == k_array_closure);
    assert (idx.val_kind == k_scalar);
    assert (idx.val_scal.val >= 0);
    switch (a.val_kind) {
    case k_evaluated_array:
        assert ((size_t)idx.val_scal.val < a.val_evarr.size);
        return mk_scalar (a.val_evarr.val[idx.val_scal.val]);
    case k_array_closure:
        assert ((size_t)idx.val_scal.val < a.val_evarr.size);
        if (a.val_clarr.mask[idx.val_scal.val])
            return mk_scalar (a.val_clarr.val[idx.val_scal.val]);
        else {
            value t = a.val_clarr.f (idx);
            assert (t.val_kind == k_scalar);
            a.val_clarr.mask[idx.val_scal.val] = true;
            a.val_clarr.val[idx.val_scal.val] = t.val_scal.val;
            return t;
        }
    default:
        abort ();
    }
}


bool
val_true (value x)
{
    assert (x.val_kind == k_scalar);
    return !!x.val_scal.val;
}


// An array to keep variable pointers at runtime.
value variables[100];

const value cst_val_0  = { .val_scal = {k_scalar, 0}};
const value cst_val_1  = { .val_scal = {k_scalar, 1}};
const value cst_val_2  = { .val_scal = {k_scalar, 2}};
const value cst_val_3  = { .val_scal = {k_scalar, 3}};
const value cst_val_99 = { .val_scal = {k_scalar, 99}};



// \x.x
value
id (value i)
{
    return i;
}

// \x.if i = 0 then 0
//    else a.(i-1)+2;
value
even (value i)
{
    value a = variables[0];
    if (val_true (eval_eq (i, cst_val_0)))
        return cst_val_3;
    else
        return eval_sel (a, eval_minus (i, cst_val_1));
}

// \i.if i = 0 then a.i
//    else if i = 99 then a.i
//    else (a.(i-1) + a.i + a.(i+1)) / 3
value
stencil (value i)
{
    value a = variables[0];

    if (val_true (eval_eq (i, cst_val_0)))
        return eval_sel (a, cst_val_0);
    else if (val_true (eval_eq (i, cst_val_99)))
        return eval_sel (a, cst_val_99);
    else {
        value t1 = eval_sel (a, eval_minus (i, cst_val_1));
        value t2 = eval_sel (a, eval_plus (i, cst_val_1));
        value t3 = eval_plus (t1, eval_sel (a, i));
        value t4 = eval_plus (t3, t2);
        return eval_div (t4, cst_val_1);
    }
}





int main (void)
{
    variables[0] = eval_imap_closure (100, even);
    value_print (variables[0]); printf ("\n");
    //variables[0] = v;
    value w = eval_imap (100, stencil);
    value_print (w); printf ("\n");
    return EXIT_SUCCESS;
}
