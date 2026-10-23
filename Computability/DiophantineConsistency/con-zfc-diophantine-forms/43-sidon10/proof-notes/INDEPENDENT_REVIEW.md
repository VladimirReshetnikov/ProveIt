# Independent review of the block compiler

Reviewed against ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`, with the exact package31 parent
quartic bytes and its complete fixed coefficient tuple.

## Conclusion

The new source compiler is sound and complete. It can replace the
power-of-five scalar source coding in the ten-integer construction while
leaving the Lucas bridge, quintic merger, and three-radicand finalizer
unchanged. The exact source polynomial identities were checked independently
in every source variable and coefficient port, not only by random evaluation.
The current arithmetic circuit's attained degree and operation counts are
recorded by `generated/INDEPENDENT_AUDIT.json`.

The proof remains an ordinary mathematical composition with the inherited
machine/compiler endpoint and Sun's stated Lucas theorems. It is not a
new Lean or Rocq end-to-end certificate. The reduction does not prove
Con(ZFC) or decide whether its polynomial has a zero.

## 1. Why the shorter block stride is valid

Let the constant digit have weight0, let the31 source digits have positive
weights at mostH, and suppose every unordered pair of32 weights has a
different sum. The independent audit checks all528 such pairs. Set

    s=2H+1, L_j=js+2H, j=0,...,21.

The j-th reversed quadratic block D_j has exponents between0 and2H.
Thus the shifted blocks B^(js)D_j have disjoint coefficient positions.
Their product with C(B)=(1+sum z_i B^w_i)^2 need not have disjoint blocks.
This does not matter. A contribution from block k to target L_j requires

    e(gamma)-e(alpha)=(j-k)s,

where both e(gamma) and e(alpha) belong to[0,2H]. Since s>2H, it follows
that j=k. The pair-sum property then gives gamma=alpha (padding with
zero-weight constant positions), so the coefficient is exactly2r_j(z).
This establishes all22 equations simultaneously without first taking a
sum of squares.

The audit reconstructs each shifted residual from the original sparse
quadratic by literal polynomial substitution. It checks the136 factorial-
weighted source records against these polynomials. It then enumerates every
possible quadratic multiplier monomial against every emitted source term,
including cross-block possibilities, and compares every extracted target
polynomial to twice the original residual. All22 symbolic identities hold.

## 2. Coefficient bounds remain uniform despite block overlap

Let A bound the absolute values of the weighted coefficients of all D_j.
The shifted D_j blocks are disjoint, so every coefficient of their sum D
still has absolute value at mostA. For decoded digits0<=z_i<b, the sum of
the nonnegative coefficients of C is

    (1+sum z_i)^2 < (31b)^2.

Hence every coefficient of C D has absolute value less than961Ab^2.
The verified source constant beta_Q=2^2134940 satisfies beta_Q>8192A.
With B=beta_Q b^2, every coefficient of C D lies strictly between-B/2
and B/2. Adding B/2 to every coefficient therefore gives actual base-B
digits in(0,B). Overlap of product blocks introduces no extra factor22
in this argument.

The actual maximum weighted coefficient has2134926 bits, and is strictly
less than2^2134927. This was recomputed using full integers, not only
symbolic bit estimates or modular images. The four fixed ports were
decompressed and their original raw and gzip hashes checked.

## 3. Exact zero tests by a shared carry mask

Let Q=21s+4H be the total product degree in the radix symbol B. Set

    J=2(1+g)^2D(B)+B sum_(t=0)^Q B^t,
    U=(B-2)sum_(j=0)^21 B^L_j.

On the decoded branch, J/2 has base-B digit B/2+2r_j(z) at each L_j,
and every digit lies in(0,B). Because b and B are powers of2, binary
addition of J and U has no carry exactly when every designated digit
of J/2 equals B/2, equivalently r_j(z)=0 for all j. Multiplication by2
does not change the existence of binary carries. The masks at different
L_j occupy different base-B blocks, so one shared no-carry condition
checks all22 residuals.

The lower mask M has base-B digit B-b at each source position and B-1
at every other position throughH. Binary no-carry addition of g and M
therefore encodes precisely the31 digits z_i in[0,b); its constant
position0 is blocked. The separate lower and upper conditions are then
packed using N0=B^(H+1), N1=4B^(Q+1), N=N0*N1, exactly as in Sun's
binary binomial-divisibility lemma.

## 4. Size and positivity hypotheses for the bridge

The fifth original residual, moved to the last block, has shifted constant
coefficient+1. Thus D has leading coefficient2. Its lower coefficients
have absolute value at mostA, so D(B)>0 whenever B>A+1.

For0<=g<2bB^H, one has1+g<=2bB^H and

    D(B) < A B^(21s+2H+1)/(B-1).

The first part of J is therefore less than

    [8Ab^2/(B-1)] B^(Q+1),

and its geometric padding is less than

    [B/(B-1)] B^(Q+1).

Because B>8192Ab^2 and b>=4 on the relevant square branch, their sum is
less than2B^(Q+1)<N1. All lower and upper masks also lie in the asserted
blocks. Thus the hypotheses0<=S,T<N of the binary binomial lemma hold.

As in the original source interface, b=1+3f and the exponent of2 in
beta_Q is even. Consequently b square and f!=0 imply b>=4, B=1 modulo3,
N=1 modulo3, and X=(N-1)R is divisible by3. The displayed lower bounds
give X>3b and Y>max(b,256). The capacity cap=bB^H remains a positive
constant times an odd positive power of b.

Conversely, any solution of the parent quadratic system gives source
digits strictly below some arbitrarily large square power b=4^k.
The all-zero source tuple is excluded by the shifted fifth residual,
so g is nonzero and, since its first allowable digit position is positive,
g>=B>b. The standard positional estimate gives g<bB^H. This supplies
the forward source witnesses with all bridge bounds.

## 5. Composition with the inherited ten-integer finalizer

Sun2026 Propositions6.1 and6.2 use the source interface just verified,
and do not use a positional recurrence5^(j+1)=5*5^j. The proof was checked
against the primary HTML source:
https://arxiv.org/html/2609.01594v2 .

The package31 finalizer uses three additional reductions, all unaffected:

- The positive bridge gives O0=f^2*l^2*Delta>0. Since Delta is a multiple
  of g and g>=b>=4, it actually gives O0>=4. This validates the Pell
  existence step in the coprime square merger.
- Sun's full residue-class interpolation supplies xi divisible by the
  already chosen nonzero z and permits the y residue needed by the
  quintic divisibility/nonvanishing merger.
- The separating norm first forces xi!=0, because otherwise it becomes
  the nonzero eighth power of the quintic homogenization. Its inherited
  weights then force all three radicands to be squares and the required
  divisibility to hold. Hence all reverse-bridge hypotheses are obtained.

The definition is consequently a completely fixed ordinary polynomial
in f,g,h,k,l,w,x,y,z,m over Z, with no variable exponent, implicit
coefficient index, radical, division, or additional existential witness.

## 6. Independent arithmetic audit

`checks/audit.py` reads the delivered JSON and coefficient bytes. It does
not import the circuit builder. Besides the source identities and fixed
hashes, it independently transcribes every displayed source, bridge and
finalizer formula, compares all76 named nodes at48 assignments over three
prime fields, and proves the circuit's degree upper bound is attained by
a nonzero leading coefficient after diagonal specialization. A nonzero
leading coefficient at even one of those primes suffices for exact degree;
all three checks passed for each finalized candidate.

Finite arithmetic checks are certificates for the stated identities and
degree; they are not evidence for the existence or nonexistence of a
solution. The universal solvability equivalence rests on Sections1-5 and
the clearly identified inherited theorems.
