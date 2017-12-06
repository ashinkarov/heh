typedef int (*int_to_int) (int);


static int
add (int x, int y)
{
    return x + y;
}


static int_to_int
add_1 (int x)
{
    int tmp (int y) { return add (x, y); };

    return &tmp;
}


int main ()
{
    int_to_int adder = add_1 (2);
    return adder (3);
}
