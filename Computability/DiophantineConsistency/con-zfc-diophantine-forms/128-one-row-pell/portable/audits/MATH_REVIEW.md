# Independent signed-domain review: 378 integer variables

## Decision and object

The endpoint `integer378` passes this independent semantic-stage
and literal-interface review. Its complete equation has 378 unrestricted
integer variables, 230 quadratic residuals, 9,421 collected quartic terms,
and coefficient height 3,054,220. The polynomial is the sum of the squares
of its literal residuals. Its signed source retains the entire 359-coordinate
normalized arithmetic body of `integer378/natural_raw`, with fresh
nonnegativity predicates; it is not a domain change without restoration.

The main new lemma is the oriented, single-row Pell bound. The composition
also uses the common factorial/binomial construction, twelve paired sign
predicates, and delayed quotient signs. The underlying square-shell C222
calculus and ZFC-refutation equivalence remain inherited ordinary theorems.
This review supplies no new Lean/Rocq object or literal encoded ZFC proof.
It neither assumes nor proves consistency.

## Both Pell coordinates from one row

Let W=2B, A-1>W^3, 1<=k_i<B, and m<=W-2. Retain a complete natural
private indexed-Pell anchor with ordinate V, and retain each principal norm
`X_i^2-(A^2-1)Y_i^2=1`, permitting both principal coordinates to be signed.
Use the single row

    V = W + sum_i[(X_i-1)^2+(Y_i-k_i)^2] + (A-1)Q,  Q>=0.

This first supplies the anchor's necessary V>=W hypothesis, so the
inherited anchor criterion yields V=Y_W(A). Write
`X_i=sigma_i X_ji(A)`, `Y_i=epsilon_i Y_ji(A)`, with `j_i>=0`.
Exactly the ordinate bound in the natural review gives `j_i<=B`:
if `j_i>=B+1`, the single squared ordinate error already exceeds V.

Modulo A-1 the two errors become

    (sigma_i-1)^2 + (epsilon_i*j_i-k_i)^2.

Their total is at most

    m[(W-1)^2+4] <= W^3-4W^2+9W-10 < W^3 < A-1.

It is a nonnegative multiple of A-1 and hence zero. Therefore
`sigma_i=epsilon_i=1` and `j_i=k_i`. The zero-index case is excluded by
positive k_i. This establishes both coordinate signs before either the
power or modular-residue graph is interpreted.

For completeness set `z=Y_(B-1)(A)>=1`. The actual squared-error sum is
at most `m(A^2+1)z^2`. On the other hand

    V=2X_B(A)Y_B(A) > 2(A-1)A^2z^2,

because `X_B>(A-1)Y_B` and `Y_B>A Y_(B-1)`. Since A>W+1 and m<=W-2,
the excess is strictly greater than W. Divisibility follows from
`X_k=1 mod(A-1)` and `Y_k=k mod(A-1)`. Thus the corresponding Q is a
nonnegative integer, and the full inherited anchor completeness supplies
its private natural witnesses. The private anchor domains have not been
relaxed by this lemma.

## The signed proof stages are acyclic

1. **Prefix.** The scalar predicates and exact nonnegative polynomial
   consequences supply all semantic frame atom signs, positive requested
   indices, and natural private frame/anchor witnesses. All six exact-power
   outputs have independent scalar guards. Four of these guards were added
   explicitly after remainder-pair compression, avoiding the cycle in which
   a denominator's positivity would depend on interpreting the very power
   that defines it. The literal frame remains the doubled sum of semantic
   atoms, including all modular numerator indices.
2. **Pell coordinates.** Apply the complete oriented single-row theorem
   above. Both coordinates in each of the fifteen seed pairs are now
   canonical and positive.
3. **Six exact powers.** Interpret them in their actual topological order:
   `(F^2+1)^t`, `B^K`, `N^K`, then the three powers of q. The first base
   is at least one, B is at least two by its raw shift, and the subsequent
   bases are positive by already interpreted powers. Thus deleting the
   separate signs of the four modulus coordinates causes no zero-base gap.
   The exact modulus identity gives `T_n=2An-n^2-1>0`, and the frame bounds
   identify the output as n^k. The quotient sign is not required for the
   congruence argument. Afterwards the Pell residue is positive and its
   remainder is the least nonnegative residue, so the quotient is natural.
4. **Twelve remainder pairs.** Each exact pair satisfies `r+s=d-1` and a
   product predicate `rs>=0`. Its denominator d is positive at this stage:
   B>=2 for the factorial pair, and a positive exact power of q for every
   modular pair. Thus the nonnegative sum and nonnegative product force
   both r,s>=0. This restores all twenty-four removed scalar signs.
5. **Remaining modular signs.** The exact-binomial output slack equals
   `q-B-1`, and `q=B^(K^2)>B` independently of the binomial's meaning, so
   this slack is natural. Modular residues are positive and the recovered
   bounds make the selected residues least nonnegative ones, forcing the
   eleven modular quotients natural. The common-root quotient is natural
   because A>W^W, q<W, and its denominator is a positive product of the
   exact digit denominators.
6. **All old source domains.** The retained literal sign derivations now
   recover every one of the original 359 natural coordinate signs. The
   complete natural arithmetic-source proof applies: decode the shared
   binomial, prove F=t!, perform reciprocal CRT range decoding, and apply
   the Horn-flow/refutation calibration. No remaining coordinate is silently
   treated as natural.

For the converse, start with the canonical natural source witnesses.
The new oriented anchor lemma gives fresh private witnesses and Q. Every
scalar target and every remainder product is nonnegative. The standard
Legendre representation `a^2+b^2+c(c+1)` supplies each new guard triple.
All quotient/restoration relations hold with their original natural
witnesses. The certified integer projection and coordinate translation
then yield a zero of the displayed 378-variable polynomial.

## Independent finite evidence

`audit_signed.py` imports no equation producer or sign-inference code.
It uses only the Python standard library and the separately authored
sparse-polynomial interface audit. It verifies the following against the
actual stored coefficient lists, rather than trusting certificate labels:

- The signed body is identical to the whole normalized natural body.
- All 250 sign-inference steps equal their claimed row rearrangements.
- For every positive-monomial rule, the exact required sign dependencies
  are precisely the variables with odd multiplicity. For every square
  rule, squaring the stated affine polynomial equals the full RHS.
- The 190 applicable prefix rules, all recorded prefix signs, and all
  semantic frame atom signs are reproduced without delayed hypotheses.
- Every seed index has a positive raw lower bound in that prefix.
- The fifteen seed X/Y coordinate maps agree exactly with the raw metadata.
- The literal full-root cap row, complete private anchor and doubled frame
  agree with the theorem (via the independent frame/cap audit).
- All 36 scalar and 12 product Legendre predicates have the exact stated
  coefficients and disjoint fresh private triples.
- All twelve actual remainder-sum identities equal denominator minus one.
- Every one of the six exact-power modulus/congruence interfaces and eleven
  modular digit/remainder interfaces equals its complete polynomial formula.
- Exactly 22 deferred modulus/quotient signs and the single output slack
  are accounted for; the post-stage closure covers every source coordinate.
- The actual guarded equation hash is the input hash of its projection
  certificate.

The guarded source hash is
`1f47d9ec926b23b7689b6e2410ada8529526d2210b5f76ad54aeb5812a51efa6`.
The machine-readable result is `SIGNED378_AUDIT.json`.

The independent contraction/projection and full-polynomial verifier retained
elsewhere in the release checks the complete signed inverse certificates,
coordinate translation and collected quartic. This review complements those
finite algebraic checks with the unbounded domain argument; neither type
of evidence is a substitute for the other.


---

# Independent review of the shared modular binomial and merged Pell bound

## Outcome

The new natural-number endpoints pass this ordinary mathematical and
literal-interface review. The final selected object is
`natural242/natural/equation.json`: 242 natural
unknowns and 190 quadratic residuals. Its independently retained collected
quartic has 9,308 terms and coefficient height 18,049,118. The preceding
unmerged composition has 243 natural unknowns, 191 residuals, 8,604 terms
and height 17,724,828. Thus the last one-row step saves one unknown and one
residual while increasing support and height. Both remain below the
inspected 261-natural predecessor in all four measures.

This is an ordinary arithmetic proof review with exact artifact checks,
not a newly checked Lean/Rocq theorem or object-language ZFC proof term.
The numerical-C222/refutation calibration remains inherited. No
consistency, optimality or worldwide-priority claim is certified here.

## Mathematical composition

The common-binomial source is the complete `shared319/direct/PROOF.md`,
with its literal builder `build_modular_factorial.py`. Its six exact powers
are the factorial numerator, reciprocal-product power, power radix, and
three distinct digit denominators. Its eleven modular requests are one
exact binomial and ten binomial divisibilities. The single exact binomial
is literally the same variable used by the squared-radius factorial
bootstrap and the reciprocal CRT product.

The old common indexed-Pell machinery can be replaced by the shared-cap
criterion from `cap261/portable/CAP_THEOREM.md`, provided every requested
index is included in the semantic frame. This is essential for modular
numerator indices: shared319 did not need them in the frame under its old
index compiler, but the new pooled argument does. The actual new code
includes them, including the derived label polynomial, in the frame only.
It does not add the derived label polynomial to the separate nine-term
CRT aggregate. That distinction preserves constructive completeness.

The actual graph has fifteen independent seed indices and no derived
index pairs. Every seed is strictly positive by its raw source definition,
without interpreting any power, factorial or binomial. Every semantic
frame atom precedes the private Pell witnesses in the graph. Thus the
frame is fixed after choosing the finite source/CRT data but before
choosing the common Pell base.

The lower frame uses `L^2-((W+1)^2-1)(WZ)^2=1`, `Z>=1`, and `A=L+sigma`
with natural sigma. Pell classification gives `L>=X_W(W+1)>=(W+1)^W`;
therefore `A-1>W^3`. The free nonnegative sigma leaves an arbitrarily large
congruence class available for the modular-root condition. Enlarging W
with the extra modular indices introduces no cycle in this argument.

After index recovery, the exact-power and modular-residue arguments are
unchanged. The power radix is bounded independently before interpreting
the first binomial; the ceiling bootstrap then proves `F=t!`. Only then
are the reciprocal product, prime-power range decoding and Horn-flow
meaning used. This order does not assume the result being decoded.

## Review of the new single-row theorem

Put W=2B and require `A-1>W^3`, `1<=k_i<B`, `m<=W-2`. Retain the complete
private indexed-Pell certificate for the anchor, and write V for its
ordinate. Replace the old aggregate bound and pooled congruence by

    V = W + sum_i (Y_i-k_i)^2 + (A-1)Q,  Q>=0.

The row first supplies V>=W, permitting the retained anchor criterion to
identify V=Y_W(A). For a signed principal ordinate, write
`Y_i=epsilon_i Y_{j_i}(A)` with `j_i>=0`. With `y=Y_B(A)` and
`x=X_B(A)`, elementary Pell identities give `y>=B`,
`(A-1)y<x<=Ay`, and `Y_2B(A)=2xy<=2Ay^2`. If `j_i>=B+1`, then

    |Y_i-k_i| > (2A-2)y+1,

whose square is strictly greater than `2Ay^2>=V`. This contradicts the
single row. Hence `0<=j_i<=B`.

Modulo A-1, the squared-error sum reduces to
`sum_i(epsilon_i*j_i-k_i)^2`. Every absolute error is at most W-1; the
sum is nonnegative and less than `W^3<A-1`. Since the row makes it
divisible by A-1, it is zero. Therefore every ordinate has the true
positive sign and exact index k_i. The trace sign remains free in the
signed version of this theorem; no later power interpretation may omit
its separate orientation argument. Natural traces already have that sign.

For completeness put `Y_i=Y_ki(A)`. Set `z=Y_(B-1)(A)>=1`. The actual
error sum is at most `m*z^2`, whereas

    Y_2B(A) > 2(A-1)*z^2 > W+m*z^2.

The last inequality follows from `A>W+1` and `m<=W-2`. Thus
`Q=(V-W-sum_i(Y_i-k_i)^2)/(A-1)` is nonnegative; it is integral by the
Pell congruences. The inherited cap completeness supplies fresh private
witnesses. Their domains have not been relaxed.

In the actual natural graph, `W=2*(2+sum of semantic atoms)`. Each seed
is one of these positive atoms, so `k_i<W/2`; the count bound follows
from the same sum. The lower frame uses this doubled W everywhere.

## Source syntax and calibration

The selected endpoint uses the `xx0` square-shell constructors, not the
Cantor formulas printed in the shared319 introductory example:

    I(x,y)=2*((x+y)^2+x),       M(x,y)=I(x,y)+1,
    A(x,y)=2*((x+y)^2+3x+4y+3), E(x,y)=A(x,y)+1.

The inherited `shell_encoding_proof.md` gives explicit inverse shell
intervals and a recursive constructor-preserving bijection fixing truth
0 and falsity 1. It separately rebuilds the guarded bundle's numeric
nonzero-product witness. This is a refutability-preserving source recoding,
not a polynomial identity with the Cantor source. The retained majorants
are regenerated with these actual constructor formulas.

## Literal checks

`audit_interfaces.py` is an independent exact sparse-polynomial interface
checker with no imports from any producer. It accepts `natural242` or `integer378` as its optional argument; its
default is `natural242`.
It checked both the old and new compositions. Specifically it checks:

- Every actual frame atom and request index, including all modular indices.
- Every raw positive seed lower bound, without semantic macro assumptions.
- The separated lower-frame equation and A=L+sigma identity.
- All three private cap norms, the positive-multiple row, and three CRT rows.
- All fifteen principal norms and the literal squared-error equation.
- The complete doubled frame and removal of the former aggregate row.
- The identical factorial/reciprocal binomial output and nine-term CRT count.
- The source/target hash binding in the natural elimination certificate.

The existing independent contraction checker separately certifies every
natural restoration and the full collected quartic, rather than sampled
values. It checks the two restorations with negative coefficients by their
actual rational sum-of-squares certificates. This review did not repeat
all normal/optimized replays because no additional finite-check risk
required another run.

The final natural equation canonical JSON hash is
`956cd7b7e57647d38c0555d99dbb489e5de5365fdf0365233e441ef96dabe646`.
The old 243-natural equation canonical JSON hash is
`408bd03ac9c39669c560de78349cb047f1e871e85ccf1f76ff3ee308ae43be6b`.
The complete machine-readable interface audit receipts are retained.
