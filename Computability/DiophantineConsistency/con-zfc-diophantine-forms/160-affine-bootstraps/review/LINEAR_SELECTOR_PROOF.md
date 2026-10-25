# A linear selector offset in the factorial-free CRT compiler

Prepared with AI assistance, 25 October 2026.

## Result and exact source change

In the incoming Factorial-Free Binomial CRT construction, replace the
selector offset R=F^2 by R=F. Retain the existing growth value

    t >= 16,  F=(2(t+1))^t.

The more economical choice F=(t+2)^t also works whenever t>=16 is even.
That variant is compatible with the affine horizon t=32h+16 after its
separate signed-power bootstrap has proved t>=16.

The resulting binomial modulus is

    B = binom(F+t,t),

rather than binom(F^2+t,t). The raw index congruence becomes
B | C+F+1. Every other use of the offset is changed by the same alias R=F;
there is no partial substitution. In the literal parent source
`direct/factorial_free_affine/raw_source.json`, the single source mutation
is row zero, R-F^2 -> R-F, where F has coordinate 3 and R has coordinate 4.
The resulting affine row allows integral monic elimination of coordinate R.

This is an existence-preserving change of the semantic compiler, not a
claimed bijection between all zeros of the old and new sources. Finite
refutations produce new witnesses using the generalized CRT construction.
Every new zero decodes to a finite refutation using that same compiler.
All subsequent factorizations and coordinate eliminations are exact zero-set
preserving algebraic steps with their own finite certificates.

## Elementary least-common-multiple bound

Write L_n=lcm(1,...,n), for n>=1. Then

    L_n <= 4^(n-1).                                      (1)

Here is a proof requiring no asymptotic prime distribution estimate.
For n>=2 put m=ceil(n/2). The integer L_n/L_m is squarefree: for every
prime p, at most one of its powers can lie in (m,n], since dividing any
such power by p gives a number at most n/2<=m.
If p divides L_n/L_m, the largest power p^a<=n lies in (m,n]. In the
Legendre-valuation expansion of binom(n,m), the summand at p^a is

    floor(n/p^a)-floor(m/p^a)-floor((n-m)/p^a)=1.

All the other summands are nonnegative, so p divides binom(n,m).
Consequently

    L_n/L_m divides binom(n,m).

The sum of the even-index binomial coefficients, and also of the odd-index
coefficients, is 2^(n-1). In particular binom(n,m)<=2^(n-1). Induction,
starting from L_1=1, gives

    L_n <= 4^(m-1) 2^(n-1) <= 4^(n-1).

The last exponent is 2n-3 for even n and 2n-2 for odd n, proving (1).

For t>=16, therefore,

    L_t^2 <= 16^(t-1) < (t+2)^t <= (2(t+1))^t.            (2)

Thus either stated growth choice satisfies the complete selector premise
F>L_t^2. This is the only new number-theoretic input needed to replace
R=F^2 by R=F in the existing prime-power CRT theorem.

## Applying the prime-power selector theorem

The inherited factorial-free theorem states that for every R>=L_t^2,
B=binom(R+t,t) has these two properties:

1. For every row i in {1,...,t}, some full prime power p^e || B satisfies
   p^e | R+i and p^e>t.
2. For every full prime power p^e || B, some row i in {1,...,t} satisfies
   p^e | R+i.

The first property recovers each bounded row from the global CRT
congruences. The second permits compatible assignments at every prime of
B in the converse CRT construction. Inequality (2) verifies both properties
for R=F. The theorem's remaining hypotheses and proof are unchanged.

For clarity, the key valuation argument in the first property is as follows.
Since R+i>L_t^2, some prime p has v=v_p(R+i)>2a, where
 a=v_p(L_t)=floor(log_p t). For j!=i the valuation of R+j is v_p(j-i).
Thus e=v_p(B)=v-d, where d=v_p(t*binom(t-1,i-1))<=a. Consequently
 e>a, e<=v, so p^e>t and p^e divides R+i. This argument depends only on the
size premise, never on R being a square.

## Soundness dependencies after the substitution

The modified first binomial upper index F+t is smaller than the old
F^2+t, because F>=1. All inherited estimates that upper-bound the latter
remain valid for the former. In particular the signed-radix bootstrap uses

    binom(F+t,j) <= (F^2+t)^t <= (F^2+F)^t <= 2^(t(F-1))
    for 0<=j<=t.

Its common-remainder argument therefore recovers
B=binom(F+t,t)>0 exactly as before. Moreover B>=F+1, so any later bound
using B>=F+1 remains valid. The raw index right side C+F+1 is positive
once C>=0, retaining the earlier B!=0 bootstrap.

The label-product separation continues to use the unchanged weight F;
it never used R. The endpoint lower bounds x>=F+1 and
x>=2+(t+1)y remain unchanged. The beta parameter y still receives its
separate sufficient multiple of F. The square frame includes the actual
requested exponent F+t and the actual remaining atoms; the smaller offset
neither omits an atom nor invalidates an upper bound.

## Constructive completeness and parity

A finite refutation is first padded to a permitted sufficiently large
horizon. Choose the stated F and choose the beta multiplier with enough
prime valuations to make the beta moduli pairwise coprime, exactly as in
the factorial-free parent (or its independently proved affine-beta variant).
Set R=F, B=binom(F+t,t) and N=B^x. Apply the generalized CRT theorem at
this B; it constructs all required representative classes modulo N^2.
The subsequent parity and divisibility adjustments change representatives
within those classes and do not require the old value of B.

In particular B is odd. Both allowed growth bases are even, so v_2(F)>=t.
For each 1<=i<=t, v_2(i)<=floor(log_2 t)<t and hence

    v_2(F+i)=v_2(i).

The numerator product (F+1)...(F+t) and denominator t! have equal
2-adic valuations. Thus v_2(B)=0. This proves the oddness needed for the
parity-selective CRT lifts, without asserting that F/i is an integer for
every i. The old square offset is unnecessary for this conclusion.

The actual CRT representatives can then be chosen with the same parity,
anchor-dominance and cofinal bounds used in the corresponding radix proof.
The new requests have their true semantic values; their canonical Pell
witnesses and common remainder witnesses follow from the same completeness
construction. This proves that every finite refutation yields a zero of
the new ordinary polynomial.

## Measured intermediate endpoints

On the existing quadratic source and inherited affine-exposure certificate,
R=F alone gives:

- sparse: 241 unrestricted integers,177 quadratic residuals,4974 collected
  quartic monomials,coefficient height7968,residual height64;
- dense: 240 unrestricted integers,176 residuals,12711 monomials,height7968.

With the independently proved q=6z+3 source replacement, before affine
horizon/beta refinements, the measured endpoints are:

- sparse:240 integers,176 residuals,5028 terms,height14688,row height84;
- dense:239 integers,175 residuals,12754 terms,height14688.

These are exact finite artifact counts, not universal lower bounds or a
global simplicity optimum. The source mutation, Horn-factorization records,
monic restoration certificates and transferred affine-row certificates are
retained under `alternative_selector/` in this working session. Later
compositions must report their own literal final counts.

## Independent review of the affine-radix argument

I independently reviewed `research_incoming/affine_radix/PROOF.md` against
the factorial-free parent interface. The sign recovery is acyclic:
q=6z+3 excludes q in {-1,0,1} and q+1 in {-1,0,1}; numerator requests force
all CRT representatives nonnegative; H>=2 and the raw index imply |BH|>=2;
the self-radix request and endpoints give x>=2+(t+1)y. The first digit is
recovered using Q=|q| and absolute low-remainder bounds before B or q is
asserted positive. The recovered B=binom(R+t,t)>0 then makes q>0.

The numerical margin is valid: Cmax<=2^(t(F-1)) and
Q>=2^((t+1)F+2) imply Cmax/(Q-1)<2^(-F-t-1)<1/32. For completeness,
when 3 does not divide B, adjusting a non-anchor representative by
0,2N^2 or4N^2 preserves its parity and CRT class and reaches every class
modulo3. Choosing the dominant odd representative a in [6N^2,8N^2),
with all others at most6N^2, preserves anchor domination and bounds
expressed in the actual H. No circular positivity premise was found.
This is an independent review within the AI-assisted workflow, not
outside human review or a proof-assistant certificate.
