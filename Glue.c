// This program by D. E. Knuth is not copyrighted and can be used freely.
// It was written on 18 Dec 1981 and revised on 24 May 1991.

// §1. Introduction.
// If ‹TeX› is being implemented on a microcomputer that does 32-bit addition and subtraction,
// but with multiplication and division restricted to multipliers and divisors that are either powers of 2 or positive integers less than 2¹⁵,
// it can still do the computations associated with the setting of glue in a suitable way.
// This program illustrates one solution to the problem.

// Another purpose of this program is to provide the first ‟short” example of the use of ‹WEB›.

// §2. The Problem and a Solution.
// We are concerned here with the ‟setting of glue” that occurs when a ‹TeX› box is being packaged.
// Let x₁, …, x_n be integers whose sum s ≡ x₁ + ⋯ + x_n is positive, and let t be another positive int.
// These x_i represent Scaled amounts of glue in units of sp (Scaled points), where one sp is 2⁻¹⁶ of a printer's point.
// The other quantity t represents the total by which the glue should stretch or shrink.
// Following the conventions of ‹TeX82›, we will assume that the integers we deal with are less than 2³¹ in absolute value.

// After the glue has been set, the actual amounts of incremental glue space (in sp)
// will be the integers f(x₁), …, f(x_n), where f is a function that we wish to compute.
// We want f(x) to be nearly proportional to x, and we also want the sum f(x₁) + ⋯ + f(x_n) to be nearly equal to t.
// If we were using floating-point arithmetic, we would simply compute f(x) ≡ (t/s)·x and hope for the best;
// but the goal here is to compute a suitable f using only the fixed-point arithmetic operations of a typical ‟16-bit microcomputer.”

// The solution adopted here is to determine integers a, b, c such that
//	f(x) ≡ ⌊2^-b c ⌊2^-a x⌋⌋
// if x is nonnegative.
// Thus, we take x and shift it right by a bits, then multiply by c (which is 2¹⁵ or less), and shift the product right by b bits.
// The quantities a, b, and c are to be chosen so that this calculation doesn't cause overflow and so that f(x₁) + ⋯ + f(x_n) is reasonably close to t.

// The following method is used to calculate a and b:
// Suppose
//	y ≡ ∨_{1 ≤ i ≤ n} |x_i|.
// Let d and e be the smallest integers such that t < 2^d s and y < 2^e.
// Since s and t are less than 2³¹, we have -30 ≤ d ≤ 31 and 1 ≤ e ≤ 31.
// An error message is given if d + e ≥ 31; in such a case some x_m has |x_m| ≥ 2^{e - 1}
// and we are trying to change |x_m| to |(t/s) x_m| ≥ 2^{d + e - 2} ≥ 2³⁰ sp, which ‹TeX› does not permit.
// (Consider, for example, the ‟worst case” situation x₁ ≡ 2³⁰ + 1, x₂ ≡ -2³⁰, t ≡ 2³¹ - 1;
// surely we need not bother trying to accommodate such anomalous combinations of values.)
// On the other hand if d + e ≤ 31, we set a ≡ e - 16 and b ≡ 31 - d - e.
// Notice that this choice of a guarantees that ⌊2^{-a} |x_i|⌋ < 2¹⁶.
// We will choose c to be at most 2¹⁵, so that the product will be less than 2³¹.

// The computation of c is the tricky part.
// The ‟ideal” value for c would be ρ ≡ 2^{a + b} t/s, since f(x) should be approximately (t/s)·x.
// Furthermore it is better to have c slightly larger than ρ, instead of slightly smaller, since the other operations in f(x) have a downward bias.
// Therefore we shall compute c ≡ ⌈ρ⌉.
// Since 2^{a + b} t/s < 2^{a + b + d} =2¹⁵, we have c ≤ 2¹⁵ as desired.

// We want to compute c ≡ ⌈ρ⌉ exactly in all cases.
// There is no difficulty if s < 2¹⁵, since c can be computed directly using the formula c ≡ ⌊ (2^{a + b} t + s - 1)/s ⌋;
// overflow will not occur since 2^{a+b} t < 2¹⁵ s < 2³⁰.

// Otherwise let s ≡ s₁ 2^l + s₂, where 2¹⁴ ≤ s₁ < 2¹⁵ and 0 ≤ s₂ < 2^l.
// We will essentially carry out a long division.
// Let t be ‟normalized” so that 2³⁰ ≤ 2^ht < 2³¹ for some h.
// Then we form the quotient and remainder of 2^h t divided by s₁,
//	2^ht ≡ qs₁ + r₀,	0 ≤ r₀ < s₁.
// It follows that 2^{h+l} t - qs ≡ 2^l r₀ - q s₂ ≡ r, say.
// If 0 ≥ r > -s we have q ≡ ⌈2^{h+l} t/s⌉; otherwise we can replace (q,r) by (q ± 1,r ∓ s) repeatedly until r is in the correct range.
// It is not difficult to prove that q needs to be increased at most once and decreased at most seven times, since 2^l r₀ - q s₂ < 2^l s₁ ≤ s
// and since q s₂/s ≤ (2^h t/s₁)(s₂/2^l s₁) < 2³¹/s₁^2 ≤ 8.
// Finally, we have a + b - h - l= -1 or -2,
// since 2^{28 + l} ≤ 2¹⁴ s ≡ 2^{a + b + d - 1}s ≤ 2^{a+b} t < 2^{a + b + d} s ≡ 2¹⁵ s < 2^{30 + l} and 2³⁰ ≤ 2^h t < 2³¹.
// Hence c ≡ ⌈2^{a + b - h - l} q⌉ ≡ ⌈½q⌉ or ⌈¼q⌉.

// An error analysis shows that these values of a, b, and c work satisfactorily, except in unusual cases where we wouldn't expect them to.
// When x ≥ 0 we have
//	f(x)	= 2^{-b} (2^{a + b} t/s + θ₀) (2^{-a} x - θ₁) - θ₂
//		= (t/s) x + θ₀ 2^{-a - b} x - θ₁ 2^a t/s - 2^{-b} θ₀ θ₁ - θ₂
// where 0 ≤ θ₀, θ₁, θ₂ < 1.
// Now 0 ≤ θ₀ 2^{-a - b} x < 2^{e - a - b} ≡ 2^{d + e - 15} and 0 ≤ θ₁ 2^a t/s < 2^{a + d} ≡ 2^{d + e - 16}, and the other two terms are negligible.
// Therefore f(x₁) + ⋯ + f(x_n) differs from t by at most about 2^{d + e - 15} n.
// Since 2^{d + e} is larger than (t/s) y, which is the largest stretching or shrinking of glue after expansion,
// the error is at worst about n/32000 times as much as this, so it is quite reasonable.
// For example, even if fill glue is being used to stretch 20 inches, the error will still be less than 1/1600 of an inch.

// To sum up: Given the positive integers s, t, and y as above, we set
//	a ≥ ts ⌊log y⌋ - 15,	b ≥ ts 29 - ⌊log y⌋ - ⌊log t/s⌋,	and	c ≥ ts ⌈2^{a + b} t/s⌉.
// The implementation below shows how to do the job in ‹Pas› without using large numbers.

// ‹TeX› wants to have the glue-setting information in a 32-bit data type called |GlueRatio|.
// The ‹Pas› implementation of ‹TeX82› has |GlueRatio ≡ real|, but alternative definitions of |GlueRatio| are explicitly allowed.

// Editor's Note:
// ∙	The field names have been changed from a_part, b_part and c_part respectively to A, B and C.

// For our purposes we shall let |GlueRatio| be a record that is packed with three fields:
//	A will hold the positive int a + 16,
//	B will hold the nonnegative int b, and
//	C will hold the nonnegative int c.
// When the formulas above tell us to take b > 30, we might as well set c = 0 instead, because f(x) will be zero in all cases when b > 30.
// Note that we have only about 25 bits of information in all, so it should fit in 32 bits with ease.

typedef struct {
   enum {1..31} A;	// the quantity e ≡ a + 16 in our derivation
   enum {0..30} B;	// the quantity b in our derivation
   enum {0..0x8000} C;	// the quantity c in our derivation
} GlueRatio;
typedef int Scaled;	// this data type is used for quantities in sp units

// The real problem is to define the procedures that ‹TeX› needs to deal with such |GlueRatio| values:
// (a)	Given Scaled numbers |s|, |t|, and |y| as above, to compute the corresponding |GlueRatio|.
// (b)	Given a nonnegative Scaled number |x| and a |GlueRatio| |Gr|, to compute the Scaled number |f(x)|.
// (c)	Given a |GlueRatio| |Gr|, to print out a decimal equivalent of |Gr| for diagnostic purposes.

// The procedures below can be incorporated into ‹TeX82› via a change file without great difficulty.
// A few modifications will be needed, because ‹TeX›'s |GlueRatio| values can be negative in unusual cases ―
// when the amount of stretchability or shrinkability is less than zero.
// Negative values in the |C| will handle such problems, if proper care is taken.
// The error message below should either become a warning message or a call to ‹TeX›'s |print_err| routine; in the latter case, an
// appropriate help message should be given, stating that glue cannot stretch to more than 18 feet long, but that it's OK to proceed with fingers crossed.

// §3. Glue Multiplication.
// The easiest procedure of the three just mentioned is the one that is needed most often, namely, the computation of |f(x)|.

// ‹Pas› doesn't have built-in binary shift commands or built-in exponentiation, although many computers do have this capability.
// Therefore our arithmetic routines use an array called ‛|Exp2|’, containing powers of two.
// Divisions by powers of two are never done in the programs below when the dividend is negative,
// so the operations can safely be replaced by right shifts on machines for which this is most appropriate.
// (Contrary to popular opinion, the operation ‛|x/2|’ is not the same as shifting |x| right one binary place,
// on a machine with two's complement arithmetic, when |x| is a negative odd int.
// But division ≪_ is _≫ equivalent to shifting when |x| is nonnegative.)
int Exp2[0x1f];	// |Exp2[k] ≡ 2^k

// The glue-multiplication function |f|, which replaces several occurrences of the ‛|float|’ macro in ‹TeX82›, is now easy to state:
int GlueMult(Scaled x, GlueRatio Gr) {	// returns f(x) as above, assuming that x ≥ 0
   if (Gr.A > 16) x /= Exp2[Gr.A - 16];	// right shift by a places
   else x *= Exp2[16 - Gr.A];	// left shift by -a places
   return x*Gr.C/Exp2[Gr.B];	// right shift by b places
}	// note that b may be as large as 30

// §4. Glue Setting.
// The GlueFix() procedure computes |a|, |b|, and |c| by the method explained above.
// ‹TeX› does not normally compute the quantity |y|, but it could be made to do so without great difficulty.

// This procedure replaces several occurrences of the ‛|unfloat|’ macro in ‹TeX82›.
// It would be written as a function that returns a |GlueRatio|, if ‹Pas› would allow functions to produce records as values.
GlueRatio GlueFix(Scaled s, Scaled t, Scaled y) {
// Normalize |s|, |t|, and |y|, computing |a|, |k|, and |h|
   int s0 = s;	// original (unnormalized) value of |s|
   int a = 15;	// a component of the desired ratio
   for (; y < 0x40000000; a↓, y += y);	// |y| is known to be positive
   int k = 0;	// 30 - ⌊log s⌋
   for (; s < 0x40000000; k↑, s += s);	// |s| is known to be positive
   int h = 0;	// 30 - ⌊log t⌋
   for (; t < 0x40000000; h↑, t += t);	// |t| is known to be positive
// now 2³⁰ ≤ t ≡ 2^h t₀ < 2³¹ and 2³⁰ ≤ s ≡ 2^k s₀ < 2³¹, hence d ≡ k - h if t/s < 1.
   int b = t < s? 15 - a - k + h: 14 - a - k + h;	// a component of the desired ratio
   int c;	// a component of the desired ratio
   if (b < 0 ∨ b > 30) {
      if (b < 0) printf("! Excessive glue.\n");	// error message
      b = 0, c = 0;	// make |f(x)| identically zero
   } else {
      if (k ≥ 16)	// easy case, s₀ < 2¹⁵
         c = (t/Exp2[h - a - b] + s0 - 1)/s0;	// here 1 ≤ h - a - b ≤ k - 14 ≤ 16.
      else {
      // Compute |c| by long division
         int w = Exp2[16 - k];	// 2^l, where l ≡ 16 - k
         int s1 = s0/w;	// divisor
         int q = t/s1;	// quotient
         int r = t%s1*w - s0%w*q;	// remainder
         if (r > 0) q↑, r -= s0;
         else for (; r ≤ -s0; q↓, r += s0);
         c = a + b + k - h ≡ 15? (q + 1)/2: (q + 3)/4;
      }
   }
   return (GlueRatio}(.A = a + 16, .B = b, .C = c};
}

// §5. Glue-Set Printing.
// The last of the three procedures we need is |PutGlueRatio|, which displays a |GlueRatio| in symbolic decimal form.
// Before constructing such a procedure, we shall consider some simpler routines, copying them from an early draft of the program ‹TeX82›.
const Scaled Scaled1 = 0x10000;	// 0x10000 ≡ (Scaled)1.0000

enum {10} Dig[0x10];	// for storing digits

// An array of digits is printed out by |PutNum|.
void PutNum(int k) {	// prints |Dig[k-1]| … |Dig[0]|
   while (k↓ > 0) putchar('0' + Dig[k]);
}

// A nonnegative int is printed out by |PutInt|.
void PutInt(int n) {	// prints an int in decimal form
   enum {13} k = 0;	// index to current digit; we assume that 0 ≤ n < 10^¹²
   do Dig[k↑] = n%10, n /= 10; while (n ≠ 0);
   PutNum(k);
}

// And here is a procedure to print a nonnegative |Scaled| number.
void PutScaled(Scaled Sc) {	// prints a Scaled real, truncated to four digits
   PutInt(Sc/Scaled1);	// print the int part
   Sc = Sc%Scaled1*10000/Scaled1;
   for (enum {4} k = 0; k < 4; Sc /= 10, k↑) Dig[k] = Sc%10;
   putchar('.'), PutNum(4);
}

// Now we're ready to print a |GlueRatio|.
// Since the effective multiplier is 2^{-a - b} c, we will display the Scaled int 2^{16 - a - b} c,
// taking care to print something special if this quantity is terribly large.
void PutGlueRatio(GlueRatio Gr) {	// prints a glue multiplier
   enum {-29..31} j = 32 - Gr.A - Gr.B;	// the amount to shift c.
   for (; j > 15; j↓) printf("2x");	// indicate multiples of 2 for BIG cases
   PutScaled(j < 0? Gr.C/Exp2[-j]: Gr.C*Exp2[j]);	// shift right if j < 0, left otherwise.
}

// §6. The Driver Program.
// In order to test these routines, we will assume that the |input| file contains a sequence of test cases,
// where each test case consists of the int numbers t, x₁, …, x_n, 0.
// The final test case should be followed by an additional zero.
Scaled x[1..1000];	// the x_i
Scaled t;		// the desired total

// Each case will be processed by the following routine, which assumes that t has already been read.
void Test(int m) {	// processes the next data set, given |t| and |m|
   printf("Test data set number %1d:\n", m);
// Read x₁, …, x_n
   enum {0..1000} n = 0;	// the number of items
   do read(x[↑n]); while (x[n] ≠ 0);
   n↓;
// Compute |s| and |y|
   Scaled s = 0;	// the sum x₁ + ⋯ + x_n
   Scaled y = 0;	// ∨_{1 ≤ i ≤ n} |x_i|
   for (enum {0..1000} k = 1; k ≤ n; k↑) {
      s += x[k];
      if (y < abs(x[k])) y = abs(x[k]);
   }
   if (s ≤ 0) printf("Invalid data (nonpositive sum); this set rejected.\n");
   else {
   // Compute Gr and print it
      GlueRatio Gr = GlueFix(s, t, y); // computed the glue multiplier Gr, perhaps print an error message
      printf("  Glue ratio is "), PutGlueRatio(Gr), printf(" (%16d,%1d,%1d)\n", Gr.A - 16, Gr.B, Gr.C);
   // Print the values of x_i, f(x_i), and the totals
      Scaled ts = 0;	// the sum f(x₁) + ⋯ + f(x_n)
      for (enum {0..1000} k = 1; k ≤ n; k↑) {
         printf("%20d", x[k]);
         y = x[k] ≥ 0? GlueMult(x[k], Gr): -GlueMult(-x[k], Gr);
         printf("%15d\n", y);
         ts += y;
      }
      printf(" Totals%13d%15d (versus %1d)\n", s, ts, t);
   }
}

// Here is the main program.
// The program itself is written in standard ‹Pas›.
// It begins with a normal program header, most of which will be filled in with other parts of this ‟web” as we are ready to introduce them.
// program GLUE(input, output);
int main(int AC, char *AV[]) {
// This procedure gets things started
   for (enum {1..30} k = 0; k < 0x1f; k↑) Exp2[k] = 1 ⊂ k;
   for (int m = 1; (read(t), t) > 0; m↑) Test(m);
}
