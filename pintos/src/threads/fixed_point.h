#define F (1 << 14) //fixed point 1
#define INT_MAX ((1 << 31) - 1)
#define INT_MIN (-(1 << 31))
// x and y denote fixed_point numbers in 17.14 format
// n is an integer

int int_to_fp(int n); /* Convert n to fixed point */
int fp_to_int_round(int x); /* Convert x to integer (rounding to nearest) */
int fp_to_int(int x); /* Convert x to integer (rounding toward zero) */
int add_fp(int x, int y); /* Add x and y */
int add_mixed(int x, int n); /* Add x and n */
int sub_fp(int x, int y); /* Subtract y from x */
int sub_mixed(int x, int n); /* Subtract n from x */
int mult_fp(int x, int y); /* Multiply x by y */
int mult_mixed(int x, int n); /* Multiply x by n */
int div_fp(int x, int y); /* Divide x by y */
int div_mixed(int x, int n); /* Divide x by n */


int int_to_fp(int n) /* Convert n to fixed point */
{
    return n * F;
}
int fp_to_int_round(int x) /* Convert x to integer (rounding to nearest) */
{
    if(x >= 0) return (x+F/2)/F;
    else return (x-F/2)/F;
}
int fp_to_int(int x) /* Convert x to integer (rounding toward zero) */
{
    return x/F;
}
int add_fp(int x, int y) /* Add x and y */
{
    return x + y;
}
int add_mixed(int x, int n) /* Add x and n */
{
    return x + n*F;
}
int sub_fp(int x, int y) /* Subtract y from x */
{
    return x - y;
}
int sub_mixed(int x, int n) /* Subtract n from x */
{
    return x-n*F;
}
int mult_fp(int x, int y) /* Multiply x by y */
{
    int64_t temp = x;
    temp = temp * y / F;
    return (int)temp;
}
int mult_mixed(int x, int n) /* Multiply x by n */
{
    return x*n;
}
int div_fp(int x, int y) /* Divide x by y */
{
    int64_t temp = x;
    temp = temp * F / y;
    return (int)temp;
}
int div_mixed(int x, int n) /* Divide x by n */
{
    return x/n;
}
