# Affine radix and an odd beta multiplier

## Exact source and change

The source is the factorial-free binomial CRT package contained in
`ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip`, at ProveIt commit
`f7ed4a58c38c2f8d897917f68e5b8eb04609bf87`, path `docs/incoming/`.
The raw arithmetic source is its
`direct/factorial_free_affine/raw_source.json`; the principal and dense
emitted equations are `direct/principal/equation.json` and
`direct/companion/equation.json`.

Replace exactly two source rows:

    q = (2z+1)^2        becomes        q = 4z+1,
    s = (2v+1)^2        becomes        s = 2v+1.

Retain the row `y=Fs` and every other arithmetic source row. In particular
retain the complete fourteen-pair signed orientation pool, square frame,
eighteen power requests, every normalized remainder and its common norm,
and the unaltered local C222 calculus.

The change is semantic: a zero of the new source need not admit a square
root of its radix or beta multiplier. Therefore it is NOT justified by
asserting a bijection to the old source. The proof below supplies new
soundness and completeness. The later affine projections ARE integral
bijections of zero sets, with explicit inverse maps.

## Notation and retained contracts

Write `t=16+h^2`, `d=2(t+1)`, `F=d^t`, `R=F^2`, and

    H = 2 + C + A_1 + ... + A_8,
    N = B^x,       q = (BH)^x,       M = q^x.

These displayed powers are meanings recovered from retained polynomial
certificates, not primitives in the emitted equation. Every unknown ranges
over the integers. The actual representatives C,A_j may be shifted by one
in the stored source coordinates; H uses the actual representatives.

The two beta endpoints are

    x = F+1+(y+1)u_0,
    x = 1+[1+(t+1)y]u_t.                                  (E)

The raw row-selection congruence is

    B h_B = C+F^2+1.                                     (I)

The common norm has the exact arithmetic meaning

    M^2 = 1+4 sum_(j=1)^11 rho_j^2+a^2+b^2+c(c+1).        (N)

The frame and orientation contracts used here are those already proved
for the unchanged signed source. Its integer W satisfies W>=258; every
actual base, index and output atom has absolute value <W; the center A
satisfies |A|>W^W; all fourteen principal Pell pairs are canonically
oriented at their signed indicated indices. None of those proofs uses the
radix square or the beta-multiplier square: all proposed atoms enter the
frame through squares. The retained literal power-interface audit checks
all eighteen requests, all frame atoms, five base moduli, fourteen paired
indices, and the derived t+1 pair. In the changed source only the two
front rows above change, so that complete interface is unchanged.

For a base n, index k and output m, the power request is

    X_k(A)+(n-A)Y_k(A) = m + (2An-n^2-1)eta.

For |n|>=2 this implies k>=0 and m=n^k. Here is the signed proof rather
than a positivity assumption: set T=2An-n^2-1. Modulo T,
(n-A)^2=A^2-1 and n(2A-n)=1. Thus the Pell expression is n^k for k>=0
and its inverse for k<0. The frame gives |T|>W^W+W. If k>=0,
|m-n^k|<W+W^W<|T|. If k=-j<0, multiplying by n^j gives
mn^j=1 because |mn^j-1|<|T|; this is impossible for integers |n|>=2.
The unit cases n=+/-1 follow by the Pell recurrence at every signed k;
we do not use a power assertion for n=0.

The denominator requests are q^t, q^(t+1), q^(y+1), q^x; the first three
have integer ratio variables v_t,v_(t+1),v_y satisfying D v_D=M. Every
normalized digit equation is v_D U=M Q+rho. As M!=0 by (N), if D!=0
then v_D!=0 and rho=v_D(U-DQ). Consequently r=rho/v_D is an INTEGER,
U=DQ+r, and |r|<|D|/2. This argument does not assume either D or M positive.

## Signed bootstrap: every boundary case

1. The known positive d and t give F=(2(t+1))^t>2^32. The new beta row
   gives y=F(2v+1), so |y|>=F and y!=0 before any sign of y is known.

2. The new radix row q=4z+1 excludes q=-2,-1,0. Its only possible unit
   value is q=1. If q=1, the numerator base q+1=2 forces every actual
   representative C,A_j to be nonnegative by the signed power lemma.
   Hence H>=2, and (I) forces B!=0 because C+F^2+1>0. Now |BH|>=2,
   so the self-radix request gives x>=0 and 1=(BH)^x. Thus x=0.
   But the last endpoint in (E) would make 1+(t+1)y divide -1. Its
   absolute value is at least (t+1)F-1>1, contradiction. This proof
   does not use y>0 or a nonnegative beta quotient.

3. Therefore Q=|q|>=3 and |q+1|>=2. All numerator requests force their
   actual upper indices, including the nine representatives and derived
   label, to be nonnegative. In particular H>=2, (I) gives B!=0, and
   |BH|>=2. Both M=q^x and q=(BH)^x are now exact, with x>=0.

4. The ratio q^(t+1)v_(t+1)=q^x implies x>=t+1: otherwise its quotient
   would have absolute value strictly between zero and one. The request
   at base q and exponent y+1 forces y+1>=0. Since y is a nonzero odd
   multiple of F>1, y>=-1 implies y>=F>0. This is the point at which
   positivity of the new, initially signed beta spacing is proved.

5. If u_0<=-1, the first endpoint gives x<=F-y<=0, contrary to x>=t+1.
   Hence x>=F+1. Since x>1 and 1+(t+1)y>0, the last endpoint forces
   u_t>=1, and

       x >= 2+(t+1)y >= 2+(t+1)F.

   Thus every exponent requested in a denominator is at most x. Put
   b=|B|. The exact self-radix gives

       Q = |BH|^x >= 2^x,       b <= |BH|/2 <= Q/2.

   In fact b<Q/2 as x>=2. No sign of B has yet been assumed.

6. Set n=F^2+t and C_j=binom(n,j). For 0<=j<=t,

       C_j <= (F^2+t)^t <= (F^2+F)^t <= 2^[t(F-1)].

   The last inequality follows from F^2+F<=2^(F-1) for F>=7. Since
   Q>=2^[2+(t+1)F], both C_t<Q/32 and C_max/(Q-1)<1/32.
   The numerator request gives U=(q+1)^n also when q is negative.
   Define the SIGNED low polynomial

       r0 = sum_(j=0)^(t-1) C_j q^j.

   Then |r0|<Q^t/32 and U congruent r0 modulo q^t. The exact normalized
   digit row gives U=q^t(B+q eta)+r with |r|<Q^t/2. Therefore r-r0 is
   a multiple of q^t with absolute value <Q^t, so r=r0. Division by
   q^t and reduction modulo q now give B congruent C_t modulo q.
   Since |B-C_t|<Q/2+Q/32<Q, B=C_t>0. Finally H>=2 and x>=t+1
   imply q=(BH)^x>0. The negative-radix cases have been excluded by
   arithmetic, without using a positive-radix expansion prematurely.

There is no zero-base use in this chain. A negative index is ruled out
only after the relevant base is known to have absolute value at least two.
The potential q=1 degeneracy is disposed of separately before recovering
the remaining index signs.

## Complete soundness after the bootstrap

At this point the unchanged factorial-free proof applies to all remaining
digits. Its hypotheses, rather than the obsolete square restrictions,
have been restored: t>=16, F=(2(t+1))^t, y>=F>0, x>=2+(t+1)y,
H>=2, B=binom(F^2+t,t)>0, q=(BH)^x>0, and all representatives and
the derived label are nonnegative. Every denominator divides q^x.

For ordinary representative a and range index j<=x,
binom(a,j)<=max(1,a)^j<=H^x, including a=j=0. The derived label has
the retained bound h_*<=H^ell, ell=4194304; x>ell(t+1). Since
q=B^x H^x and B>=2, every genuine low residue has size <D/32.
The centered common norm therefore recovers every exact binomial range.

The same local bound as the predecessor holds: with
Rmaj=2+t+x+y+F, one has Rmaj<2x and x>2^32; the fixed exponent
E=8388608 satisfies Rmaj^E<2^x. The generalized binomial CRT theorem
then decodes every row. Its radius hypothesis F^2>=lcm(1,...,t)^2
holds because F>t!. Its prime-power selectors and completeness at every
prime of B are unchanged.

The possible boundary y=F is excluded after row decoding, as in the
factorial-free predecessor: the first beta endpoint has ordinary remainder
zero, so the initial accumulator is zero. Every update
S_(i+1)(1+v_i F)=S_i(1+p_i F)(1+q_i F) has positive weights, so zero
propagates. The last endpoint has ordinary remainder one, contradiction.
Thus y>F, the first accumulator is F+1, and multiplying updates gives

    product_(i<t)(1+v_i F)
       = (1+F) product_(i<t)(1+p_i F)(1+q_i F).

The retained bounded-label polynomial-identity argument applies since
F>(t+1)^t. It recovers the required multiplicity balance. The
single-conclusion closure argument then gives a finite C222 refutation.
The retained interfaces `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` yield a finite
syntactic ZFC refutation.

## Constructive completeness

Start with a finite calibrated C222 refutation. Choose a cofinal horizon
t=16+h^2 beyond the proof tree, labels, schema data and local label sums.
Set F=(2(t+1))^t and construct its finite pending-multiset accumulators.
Let O be the odd part of t!. Choose a sufficiently large positive odd
multiple w of O and put y=Fw. Then v=(w-1)/2 is an integer satisfying
the NEW beta row. Since v_2(F)=t[1+v_2(t+1)]>v_2(t!), the integer y
is an even multiple of t!. Choose w large enough that y>F and every
accumulator is at most y.

The beta moduli 1+(i+1)y are now odd and pairwise coprime. Their CRT
period is odd, so a valid beta code x can be chosen even and arbitrarily
large, preserving every inherited bound. Set B=binom(F^2+t,t), N=B^x.
For 1<=i<=t, v_2(F^2)>floor(log_2 t) gives v_2(F^2+i)=v_2(i), hence
B and N^2 are odd. The predecessor's generalized binomial CRT now
supplies all representative classes modulo N^2. Odd N^2 permits their
parities to be chosen freely.

Use its same dominant representative a odd in [2N^2,4N^2), and the
other eight representatives even in (0,2N^2]. Then H=2+sum a_j is
odd, while the semantic anchor is even and retains its bound h_*>=2a^2.
All strict index-compatibility and coefficient-margin hypotheses from the
predecessor remain valid. Since x is even and BH odd,

    q=(BH)^x is an odd square, hence q congruent 1 modulo 8.

In particular z=(q-1)/4 is an integer satisfying the NEW radix row.
This uses square values for a completeness witness, without requiring
every zero of the new source to be a square.

All unchanged canonical Pell witnesses, exact digit witnesses, and ratio
variables exist by the retained construction. Each of the eleven actual
normalized residues has absolute value <M/32, so their squared sum
leaves a nonnegative integer gap in (N). That gap is represented by
a^2+b^2+c(c+1), as follows from the three-square theorem applied to
4g+1. Thus the complete changed arithmetic source has a zero.

All of the arguments above are finite arithmetic formalizable in ZFC.
They establish both directions of the equivalence between a zero and a
finite ZFC refutation; they decide neither consistency nor inconsistency.

## Exact emitted equations and projection

In the principal predecessor, the actual radix is x_104-1, z=x_239,
s=x_240, and v=x_241. Its final two rows are

    x_104-2-4x_239-4x_239^2,
    x_240-1-4x_241-4x_241^2.

Replace them by x_104-2-4x_239 and x_240-1-2x_241. The inverse
affine assignments x_104=2+4x_239 and x_240=1+2x_241 allow deleting
these two coordinates and rows; substitute in every other residual and
renumber in increasing old-coordinate order. Every remaining residual
is quadratic. The resulting principal has 240 integer variables,
176 rows, 5061 collected quartic monomials, coefficient height7968,
and maximum residual coefficient64.

The dense predecessor uses the same formulas with q index103,
z index238, s index239, v index240. The same exact procedure yields
239 integer variables, 175 rows, 12806 monomials, height7968, and
maximum residual coefficient64. In either case the polynomial is the
sum of squares of the complete supplied residual list.

These final-row changes faithfully implement the raw changes. The raw
q and multiplier variables and their parameter variables survive every
old monic projection. The old Horn factorization does not change the
two raw terminal rows. The predecessor's coordinate translations shift
q by -1 and leave s,z,v fixed; its six coordinate shears involve none
of those four variables. Its affine exposures and final row operations
neither use nor alter the terminal q and s rows. The complete finite
lineage check is supplied separately; no semantic inference is made
from a matching count alone.

The previous factorial-free equations had 242 variables/178 rows/5018
terms and 241 variables/177 rows/12774 terms, both height7968.
Therefore both new equations save two variables and two rows at unchanged
degree and height, with increases43 and32 in collected support. Neither
comparison is a claim of a metric-independent optimum.

## Scope

The construction retains its named Pell, generalized-binomial-CRT,
proof-calculus, and logical-calibration dependencies. It is an ordinary
unbounded proof plus exact finite artifacts, not a freshly compiled
end-to-end Lean/Rocq theorem or an emitted object-language ZFC proof.
The two affine projections and fully collected coefficients are checked
by a separate finite verifier which imports no construction code.
