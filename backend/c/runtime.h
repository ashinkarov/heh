#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdbool.h>

#ifdef GC
#include <gc.h>

#define malloc(__x) GC_MALLOC_ATOMIC (__x)
#endif

enum value_kind {
    k_scalar,
    k_array,
    k_fun,
};

struct value_scalar {
    enum value_kind kind;
    size_t val;
};

struct value_array {
    enum value_kind kind;
    size_t dim;
    size_t *shape;
    size_t *val;
};


union value_union {
    enum value_kind val_kind;
    struct value_scalar val_scal;
    struct value_array val_arr;
};

typedef union value_union value;

#define VALUE_KIND(__v) ((__v).val_kind)
#define VALUE_DIM(__v) (VALUE_KIND (__v) == k_array ? (__v).val_arr.dim : 0)

static inline size_t
prod (size_t sz, size_t *shape) {
    size_t res = 1;
    for (size_t i = 0; i < sz; i++)
        res *= shape[i];

    return res;
}

static inline size_t
idx_to_offset (size_t len, size_t *shp, size_t *idx) {
    size_t res = 0;
    size_t mul = 1;
    // XXX this is a hack
    for (ssize_t i = len-1; i >= 0; i--) {
        res += idx[i] * mul;
        mul *= shp[i];
    }
    return res;
}

static inline void
print_vec (size_t l, size_t *v)
{
    printf ("[");
    for (size_t i = 0; i < l; i++)
        printf ("%zu%s", v[i], i == l-1 ? "" : ", ");
    printf ("]");
}


static inline void
print_value (value v)
{
    switch (VALUE_KIND (v)) {
    case k_scalar:
        printf ("%zu\n", v.val_scal.val);
        break;
    case k_array:
        printf ("<");
        print_vec (v.val_arr.dim, v.val_arr.shape);
        size_t len = prod (v.val_arr.dim, v.val_arr.shape);
        const size_t lim = 25;
        bool too_long_p = len > lim;
        size_t l = too_long_p ? lim : len;
        printf (", [");
        for (size_t i = 0; i < l; i++)
            printf ("%zu%s", v.val_arr.val[i],
                    i < l-1 ? ", "
                            : too_long_p ? ", ..."
                                         : "");
        printf ("]>\n");
        break;
    default:
        assert (0);
    }
}


static inline value
mk_array (size_t dim, size_t *shape)
{
    //printf ("dim: %zu, ", dim);
    //print_vec (dim, shape);

    struct value_array va;
    va.kind = k_array;
    va.dim = dim;
    va.shape = malloc (sizeof (size_t) * dim);
    memcpy (va.shape, shape, sizeof (size_t) * dim);
    va.val = malloc (sizeof (size_t) * prod (dim, shape));
    return (value)va;
}

static inline value
mk_array_val (size_t dim, size_t *shape, size_t *val)
{
    value v = mk_array (dim, shape);
    memcpy (v.val_arr.val, val, sizeof (size_t) * prod (dim, shape));
    return v;
}


static inline value
mk_scalar (int val)
{
    struct value_scalar vs;
    vs.kind = k_scalar;
    vs.val = val;
    return (value)vs;
}

#define SCAL_BIN_FUN(name, op)                              \
static inline value                                         \
eval_ ## name (value l, value r)                            \
{                                                           \
    assert (l.val_kind == k_scalar);                        \
    assert (r.val_kind == k_scalar);                        \
    return mk_scalar (l.val_scal.val op r.val_scal.val);    \
}

SCAL_BIN_FUN (plus, +)
SCAL_BIN_FUN (minus, -)
SCAL_BIN_FUN (div, /)
SCAL_BIN_FUN (mod, %)
SCAL_BIN_FUN (mult, *)
SCAL_BIN_FUN (lt, <)
SCAL_BIN_FUN (le, <=)
SCAL_BIN_FUN (gt, >)
SCAL_BIN_FUN (ge, >=)
SCAL_BIN_FUN (eq, ==)
SCAL_BIN_FUN (ne, !=)

static inline value
eval_sel (value a, value idx)
{
    assert (idx.val_kind == k_array && VALUE_DIM (idx) == 1);
    if (VALUE_KIND (a) == k_scalar) {
        assert (a.val_arr.shape[0] == 0);
        return a;
    } else {
        size_t off = idx_to_offset (VALUE_DIM (a), a.val_arr.shape, idx.val_arr.val);
        return mk_scalar (a.val_arr.val[off]);
    }
}

// Helper function that implements a[idx] = v.
//      `a` is a genenral value (including scalars).
//      `idx` is a partial index into `a` represented as
//            a vector of indexes.
//      `len` is the length of idx vector
//      `v` is the value we are assigning.
static inline void
modarray (value a, size_t len, size_t *idx, value v)
{
    if (VALUE_KIND (a) == k_scalar) {
        assert (len == 0);
        assert (VALUE_KIND (v) == k_scalar);
        a.val_scal.val = v.val_scal.val;
        return;
    }

    if (VALUE_KIND (a) == k_array && VALUE_KIND (v) == k_scalar) {
        assert (a.val_arr.dim == len);
        size_t off = idx_to_offset (VALUE_DIM (a), a.val_arr.shape, idx);
        a.val_arr.val[off] = v.val_scal.val;
        return;
    }

    // Now we deal with the general case when `a` and `v` are both arrays.
    if (VALUE_KIND (a) == k_array && VALUE_KIND (v) == k_array) {
        // Check that the dimensionality of the `v` is correct.
        assert (a.val_arr.dim >= len
                && a.val_arr.dim - len == v.val_arr.dim);

        // Check that the shape of `v` matches `a[idx]`.
        assert (!memcmp (&a.val_arr.shape[len],
                         v.val_arr.shape,
                         sizeof (size_t) * v.val_arr.dim));

        size_t prodv = prod (v.val_arr.dim, v.val_arr.shape);
        size_t off = prodv * idx_to_offset (len, a.val_arr.shape, idx);
        memcpy (&a.val_arr.val[off], v.val_arr.val, sizeof (size_t) * prodv);
        return;
    }

    assert (0);
}

// Helper function that makes an empty array of shape `sh`.
static inline value
mk_array_or_scal (value sh)
{
    //printf ("shape: "); print_value (sh);

    assert (VALUE_KIND (sh) == k_array && sh.val_arr.dim == 1);
    size_t len = sh.val_arr.shape[0];
    if (len == 0)
        return mk_scalar (0);
    else
        return mk_array (len, sh.val_arr.val);
}


struct iterator {
    size_t len;
    size_t *start;
    size_t *val;
    size_t *stop;
    bool done;
};


static inline void
iterator_next (struct iterator *it)
{
    assert (!it->done);
    //printf ("val: ");
    //print_vec (it->len, it->val);
    //printf ("shape: ");
    //print_vec (it->len, it->shp);

    // XXX this is a hack
    for (ssize_t i = it->len - 1; i >= 0; i--) {
        if (it->val[i] + 1 >= it->stop[i])
            it->val[i] = it->start[i];
        else {
            it->val[i] += 1;
            //print_vec (it->len, it->val);
            return;
        }
    }

    //print_vec (it->len, it->val);
    it->done = true;
}

#define ITERATOR_NEXT(__it) __extension__               \
({                                                      \
    bool __done = true;                                 \
    for (ssize_t i = __it.len - 1; i >= 0; i--) {       \
        if (__it.val[i] + 1 >= __it.stop[i])            \
            __it.val[i] = __it.start[i];                \
        else {                                          \
            __it.val[i] += 1;                           \
            __done = false;                             \
            break;                                      \
        }                                               \
    }                                                   \
    __it.done = __done;                                 \
    1;                                               \
})

static inline bool
iterator_empty (size_t dim, size_t *start, size_t *end) {
    for (size_t i = 0; i < dim; i++)
        if (start[i] >= end[i])
            return true;

    return false;
}


#define CONST_VEC(...) ((size_t []){__VA_ARGS__})
#define PLUS(x, y) ((x) + (y))
#define ARRAY_VALUE(v) (v.val_arr.val)
#define MK_EMPTY_VECTOR() mk_array_val (1, CONST_VEC (0), NULL)

static inline value
shape_concat (value v1, value v2)
{
    assert (VALUE_KIND (v1) == k_array);
    assert (v1.val_arr.dim == 1);
    assert (VALUE_KIND (v2) == k_array);
    assert (v2.val_arr.dim == 1);

    //printf ("cons v1: "); print_value (v1);

    size_t len1 = v1.val_arr.shape[0];
    size_t len2 = v2.val_arr.shape[0];
    size_t *res = malloc (sizeof (size_t) * (len1 + len2));
    memcpy (res, v1.val_arr.val, sizeof (size_t) * len1);
    memcpy (&res[len1], v2.val_arr.val, sizeof (size_t) * len2);

    size_t *shape = malloc (sizeof (size_t));
    shape[0] = len1 + len2;

    return (value)(struct value_array) {
              .kind = k_array,
              .dim = 1,
              .shape = shape,
              .val = res
           };

}

static inline value
shape (value v)
{
    value res;

    switch (VALUE_KIND (v)) {
    case k_scalar:
        return mk_array_val (1, CONST_VEC (1), CONST_VEC (0));
    case k_array:
        res = mk_array (1, CONST_VEC (v.val_arr.dim));
        memcpy (res.val_arr.val, v.val_arr.shape, sizeof (size_t) * v.val_arr.dim);
        return res;
    default:
        assert (0);
    }
}

static inline value
is_limit_ordinal (value v)
{
    (void) v;
    return mk_scalar (0);
}

static inline bool
val_true (value v)
{
    assert (VALUE_KIND (v) == k_scalar);
    return !!v.val_scal.val;
}

#define ALLOC_ITERATOR_PARTS(dim_var, empty_var, val_var, dim_val) \
bool empty_var;                                         \
size_t dim_var = dim_val;                               \
size_t val_var[dim_var];

#define COPY_VEC_FROM_VAL(__dim, __v, __val)                  \
do {                                                    \
    assert (VALUE_KIND (__val) == k_array);               \
    assert (__val.val_arr.dim == 1);                      \
    memcpy (__v, __val.val_arr.val,                         \
            sizeof (size_t) * __val.val_arr.shape[0]);    \
} while (0)

#define ITERATOR_LOOP(it_var, empty_p, dim_val, start_vec, val_vec, end_vec)\
for (struct iterator it_var = {                         \
        .len = dim_val, .start = start_vec,             \
        .val = val_vec, .stop = end_vec,                 \
        .done = false};                                 \
     !empty_p && !it_var.done;                          \
     iterator_next (&it_var))

#define ITERATOR_TO_IDX(__it)                         \
((value)(struct value_array) {                          \
    .kind = k_array, .dim = 1,                          \
    .shape = CONST_VEC ((__it).len),                    \
    .val = (__it).val })

#define ITERATOR_VALUE(__it) (__it.val)


#define REDUCE_LOOP(__arr, __neut, __func, __res) \
do { \
    if (VALUE_KIND (__arr) == k_scalar) \
        __res = __func (__neut, __arr); \
    else { \
        __res = __neut; \
        for (size_t i = 0; \
             i < prod (__arr.val_arr.dim, __arr.val_arr.shape); i++)  \
            __res = __func (__res, mk_scalar (__arr.val_arr.val[i]));   \
    } \
} while (0)

#define FILTER_LOOP(__arr, __func, __res) \
do { \
    assert (VALUE_KIND (__arr) == k_array); \
    assert (__arr.val_arr.dim == 1); \
    __res = mk_array (1, __arr.val_arr.shape); \
    size_t count = 0; \
    for (size_t i = 0; i < __arr.val_arr.shape[0]; i++) {  \
        size_t el = __arr.val_arr.val[i]; \
        if (val_true (__func (mk_scalar (el))))   \
            __res.val_arr.val[count++] = el;  \
    } \
    __res.val_arr.shape[0] = count; \
} while (0)
