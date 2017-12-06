#include <functional>

int add (int a, int b) {
    return a + b;
}

int sub (int a, int b) {
    return a - b;
}

auto add_1 (int x) {
    return [x](int y)->int { return add (x, y); };
}

int foo (std::function <int(int)> f, int x)
{
    return f (x + 1);
}

int inc (int x) {
    return x + 1;
}

int main (int argc, char *argv[])
{
    return argc > 1 ? foo (add_1 (argc), 2)
                    : foo (inc, argc);
}
