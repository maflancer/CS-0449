/*
 * CS:APP Data Lab
 *
 * < Matthew Flancer    MAF291>
 *
 * bits.c - Source file with your solutions to the Lab.
 *          This is the file you will hand in to your instructor.
 *
 * WARNING: Do not include the <stdio.h> header; it confuses the dlc
 * compiler. You can still use printf for debugging without including
 * <stdio.h>, although you might get a compiler warning. In general,
 * it's not good practice to ignore compiler warnings, but in this
 * case it's OK.
 */

#ifndef COMMON_H
#include "common.h"
#endif

#if 0
/*
 * Instructions to Students:
 *
 * STEP 1: Read the following instructions carefully.
 */

You will provide your solution to the Data Lab by
editing the collection of functions in this source file.

INTEGER CODING RULES:

  Replace the "return" statement in each function with one
  or more lines of C code that implements the function. Your code
  must conform to the following style:

  int Funct(arg1, arg2, ...) {
      /* brief description of how your implementation works */
      int var1 = Expr1;
      ...
      int varM = ExprM;

      varJ = ExprJ;
      ...
      varN = ExprN;
      return ExprR;
  }

  Each "Expr" is an expression using ONLY the following:
  1. Integer constants 0 through 255 (0xFF), inclusive. You are
     not allowed to use big constants such as 0xffffffff.
     However, you are allowed to combine constants to values greater
     than 255 or less than 0. e.g. 250 + 250 = 500, so long as
     the operator you are using to combine the constants is listed as
     "legal" at the top of the method you are writing.
  2. Function arguments and local variables (no global variables).
  3. Any operators listed as "legal" at the top of the method you are writing.
  4. Shorthand versions of "legal" operators (ex. you can use ++ and += if + is legal)

  Some of the problems restrict the set of allowed operators even further.
  Each "Expr" may consist of multiple operators. You are not restricted to
  one operator per line.

  You are expressly forbidden to:
  1. Use any control constructs such as if, do, while, for, switch, etc.
  2. Define or use any macros.
  3. Define any additional functions in this file.
  4. Call any functions.
  5. Use any other operations, such as &&, ||, -, or ?:
  6. Use any form of casting.
  7. Use any data type other than int.  This implies that you
     cannot use arrays, structs, or unions.


  You may assume that your machine:
  1. Uses 2s complement, 32-bit representations of integers.
  2. Performs right shifts arithmetically.
  3. Has unpredictable behavior when shifting if the shift amount
     is less than 0 or greater than 31.


EXAMPLES OF ACCEPTABLE CODING STYLE:
  /*
   * pow2plus1 - returns 2^x + 1, where 0 <= x <= 31
   */
  int pow2plus1(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     return (1 << x) + 1;
  }

  /*
   * pow2plus4 - returns 2^x + 4, where 0 <= x <= 31
   */
  int pow2plus4(int x) {
     /* exploit ability of shifts to compute powers of 2 */
     int result = (1 << x);
     result += 4;
     return result;
  }


NOTES:
  1. Use the dlc (data lab checker) compiler (described in the handout) to
     check the legality of your solutions.
  2. Each function has a maximum number of operations (integer, logical,
     or comparison) that you are allowed to use for your implementation
     of the function.  The max operator count is checked by dlc.
     Note that assignment ('=') is not counted; you may use as many of
     these as you want without penalty.
  3. Use the btest test harness to check your functions for correctness.
  4. The maximum number of ops for each function is given in the
     header comment for each function. If there are any inconsistencies
     between the maximum ops in the writeup and in this file, consider
     this file the authoritative source.
  5. Write comments for your functions! These won't be graded, but it's good
     practice to write comments and may help you debug your code. See the
     above example to see what the comments should look like.

/*
 * STEP 2: Modify the following functions according the coding rules.
 *
 *   IMPORTANT. TO AVOID GRADING SURPRISES:
 *   1. Use the dlc compiler to check that your solutions conform
 *      to the coding rules.
 */
#endif

/*
 * bitAnd - x&y using only ~ and |
 *   Example: bitAnd(6, 5) = 4
 *   Legal ops: ~ |
 *   Max ops: 8
 *   Rating: 1
 */
int bitAnd(int x, int y) {
  int a = ~x;
  int b = ~y;

  int c = a | b;  //used de morgans law to get x & y  == ~(~x | ~y)

  int result = ~c;

  return result;
}
/*
 * bitXor - x^y using only ~ and &
 *   Example: bitXor(4, 5) = 1
 *   Legal ops: ~ &
 *   Max ops: 14
 *   Rating: 1
 */
int bitXor(int x, int y) {
  int a = ~x;
  int b = ~y;

  int c = (a & b);
  int d = ~c;         //used de morgans law to get x ^ y == ~(x &  y) & ~(~x & ~y)

  int e = x & y;
  int f = ~e;

  int result = d & f;

  return result;
}
/*
 * getByte - Extract byte n from word x
 *   Bytes numbered from 0 (least significant) to 3 (most significant)
 *   Examples: getByte(0x12345678,1) = 0x56
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 6
 *   Rating: 2
 */
int getByte(int x, int n) {
  int a = n << 3; //8n

  int b = x >> a;  //x >> 8*n

  int c = b & 0xFF; // (x >> 8*n) & 0xFF

  return c;
}
/*
 * invert - Return x with the n bits that begin at position p inverted
 *          (i.e., turn 0 into 1 and vice versa) and the rest left
 *          unchanged. Consider the indices of x to begin with the low-order
 *          bit numbered as 0.
 *   Can assume that 0 <= n <= 31 and 0 <= p <= 31
 *   Example: invert(0x80000000, 0, 1) = 0x80000001,
 *            invert(0x0000008e, 3, 3) = 0x000000b6,
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 20
 *   Rating: 3
*/
int invert(int x, int p, int n) {
  int a = ~0 << n;   // sets a to all 1s and then shifts it left by n so there will be n 0s
  int b = ~a;        //sets b to a mask where it is all 0s except for n 1s

  int c = b << p;  //this shifts the n 1s to the correct position

  return x ^ c;   //this applies the mask to x
}
/*
 * sign - return 1 if positive, 0 if zero, and -1 if negative
 *  Examples: sign(130) = 1
 *            sign(-23) = -1
 *  Legal ops: ! ~ & ^ | + << >>
 *  Max ops: 10
 *  Rating: 2
 */
int sign(int x) {
  int a = x >> 31; //will return 0 for positive numbers/zero      returns -1 for negative numbers

  int b = !!x;    //if 0 will return false   if positive will return 1       if negative wil return 1

  return a | b;  //if positive will be 0 | 1     if zero will be 0 | 0     if negative will be    -1 | 1
}
/*
 * addOK - Determine if can compute x+y without overflow
 *   Example: addOK(0x80000000,0x80000000) = 0,
 *            addOK(0x80000000,0x70000000) = 1,
 *   Legal ops: ! ~ & ^ | + << >>
 *   Max ops: 20
 *   Rating: 3
 */
int addOK(int x, int y) {
  int a = x >> 31;  //gets sign bit
  int b = y >> 31;

  int c = x + y;
  int d = c >> 31; //gets sign bit of x + y

  int e = !!(a ^ b); //checks if x and y are same sign or opposite sign   - if opposites then no overflow

  int f = !(a ^ d); //checks if x and x + y are same sign or opposite sign
  int g = !(b ^ d); //checks if y and x + y are same sign or opposite sign

  int h = f & g; //returns if x and y and x+y are opposite signs -   if x and y are same sign and x+y is opposite sign, then overflow

  return e | h;
}

#if 0
FLOATING POINT CODING RULES

For the problems that require you to implement floating-point operations,
the coding rules are less strict.  You are allowed to use looping and
conditional control.  You are allowed to use both ints and unsigneds.
You can use arbitrary integer and unsigned constants. You can use any arithmetic,
logical, or comparison operations on int or unsigned data.

You are expressly forbidden to:
  1. Define or use any macros.
  2. Define any additional functions in this file.
  3. Call any functions.
  4. Use any form of casting.
  5. Use any data type other than int or unsigned.  This means that you
     cannot use arrays, structs, or unions.
  6. Use any floating point data types, operations, or constants.
#endif

/*
 * floatNegate - Return bit-level equivalent of expression -f for
 *   floating point argument f.
 *   Both the argument and result are passed as unsigned int's, but
 *   they are to be interpreted as the bit-level representations of
 *   single-precision floating point values.
 *   When argument is NaN, return argument.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *     Comparison operations incl ==, < ,>, >=, <=
 *   Max ops: 10
 *   Rating: 2
 */
unsigned floatNegate(unsigned uf) {
  unsigned a = (0x80000000 ^ uf);  //use 0x80000000 because 8 == 1000 so it flips the sign bit
  if((uf & 0x7FFFFFFF) > 0x7F800000){ // checks for nan ,   uf & with 0x7FFFFFFF will return uf but with the sign bit as 0
    return uf;                        //                    checks if that number is > positive infinity
  }                                   //
  return a;                           //if not nan, return a
}
/*
 * floatIsEqual - Compute f == g for floating point arguments f and g.
 *   Both the arguments are passed as unsigned int's, but
 *   they are to be interpreted as the bit-level representations of
 *   single-precision floating point values.
 *   If either argument is NaN, return 0.
 *   +0 and -0 are considered equal.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *   Comparison operations incl ==, < ,>, >=, <=
 *   Legal constants: arbitrary integer and unsigned integer constants
 *   Max ops: 25
 *   Rating: 2
 */
int floatIsEqual(unsigned uf, unsigned ug) {
    int a = uf == ug;   //1 if equal or 0 if not equal

    int b = !((uf | ug) << 1); //checks if both uf and ug are 0

    if((uf & 0x7FFFFFFF) > 0x7F800000 || (ug & 0x7FFFFFFF) > 0x7F800000){  //if either argument is nan
      return 0;
    }

    return a || b;
}
/*
 *
 * !! EXTRA CREDIT !!
 *
 * floatInt2Float - Return bit-level equivalent of expression (float) x
 *   Result is returned as unsigned int, but
 *   it is to be interpreted as the bit-level representation of a
 *   single-precision floating point values.
 *   Legal ops: Any integer/unsigned operations incl. ||, &&. also if, while
 *     Comparison operations incl ==, < ,>, >=, <=
 *   Max ops: 30
 *   Rating: 4
 */
unsigned floatInt2Float(int x) {
  return 2;
}
