# Independent review of the oriented five-base pool

Prepared within the AI-assisted research workflow on 25 October 2026.
This is a separately assigned mathematical and literal-artifact review, not
external human peer review and not a new Lean/Rocq proof-assistant build.

## Verdict and precise scope

The oriented reciprocal theorem in `ORIENTED_POOLING.md` is valid
under its stated canonical signed-Pell and square-frame hypotheses. The
zero-base clause is essential and sufficient to avoid circularity in the
source sign bootstrap. I independently reconstructed the P216 semantic
ports and the retained square-frame and canonical-index aggregate. All
these identities use only rows that remain in the proposed P207 system.

The exact P207 arithmetic DAG was checked against the independently
reconstructed ports without importing the producer. Its 143 retained
quadratic residuals are exactly the parent residuals after the specified
coordinate deletion, and its final residual is exactly the claimed
oriented five-base expression. Its exact degree is 24. The finite checks
were run in ordinary and optimized Python; checks use exceptions, not
assertions. Their receipts identify which runs actually completed.

The inherited unbounded canonical signed-index theorem and the original
C222/ZF/ZFC refutation calibration remain named mathematical dependencies.
Neither the finite checker nor this review independently recompiles their
full transitive formal development. The package must preserve this boundary.

## 1. Why the single reciprocal equation works

For each base n, set T=2An-n²-1. For n=0, T=-1. For n nonzero, the frame
assumptions n²<W and |A|>W^W imply

    |T| >= 2|A|-W > W^W,
    sign(T)=sign(A n).

Thus no denominator vanishes, including at zero bases. In particular the
product of all five denominators may be cancelled in the proof; this is
not an unstated nonvanishing assumption in the final polynomial.

For each request define δ=m-X+(A-n)Y. The identity

    Σ δ² = E-T Σ Y²

is exact. Consequently the proposed global residual says that
Σ_j n_j Σ_i δ_i²/T_j is an integer. This implication uses no coprimality
between different denominators.

Let b=floor(sqrt(W-1)). Remove zero bases from the clearing product, and
put C=product(n_j^b) over the remaining blocks. Then C is a nonzero integer
unless there are no nonzero blocks, in which case the product is one.
For each nonzero block put

    d_i=C m_i-(C/n_j^b)n_j^(b+k_i).

Both terms are integers. The exponent b+k_i is nonnegative, because the
actual signed index is among the squared frame atoms. The Pell congruence
and T_j=-1 modulo n_j give Cδ_i=d_i modulo T_j, even for negative indices.
Multiplying the preceding integral rational sum by C², and replacing
each squared numerator by its congruent d_i², proves

    V=Σ_j n_j Σ_i d_i²/T_j is an integer.

This is a congruence modulo the integers between rational sums. It does
not falsely infer divisibility by each denominator from integrality of
the sum. That distinction is the main potential failure point and is
handled correctly in the proof.

If s<=5 is the number of nonzero blocks and r<=17 the total request
count, the stated estimate follows from

    |d_i| <= b^(s b+1)+b^((s+1)b) <= 2b^((s+1)b).

Therefore

    Σ |n_j|d_i² <=68 b^(12b+1)<W^(6b+2)<=W^W.

Here b>=16, 68<W, b²<W, and 6b+2<=b²+1<=W. Comparing each denominator
with W^W gives |V|<1. Thus V=0. Every nonzero summand has sign sign(A),
since n_j/T_j has that sign, so cancellation of nonzero errors is
impossible. This proves every d_i=0 and hence every requested exact
power at a nonzero base. Negative nonunit-base indices are impossible
because an integer multiple of a nonunit power cannot be one.

Conversely exact powers at nonzero bases give T_j|δ_i and hence T_j|E_j.
Then z=Σ n_j E_j/T_j is integral and supplies the new residual. Zero
bases have zero coefficient in the sum and create no condition to prove.

The proof works for negative A, negative bases, unit bases, repeated
bases and noncoprime denominators. No probabilistic or finite testing
assumption enters this argument.

## 2. Exact source deletion and port offsets

The source is the Pooled Projection incoming archive's P216 equation,
whose literal SHA-256 is

    a91308bd0c82182ea15080763cb23cb4fa0aa45a812eabb7a6cbcd21c0b95a06.

Coordinates 141--146 and 212--215 occur only in rows 97--102 and
149--152. All indices in this paragraph refer to the original P216
coordinate order and are zero based. Removing these ten rows and ten
coordinates leaves 143 quadratic residuals in 206 coordinates. One new
integer z and one new residual yield 207 variables and 144 residuals.

Important affine offsets are:

* A=x134+1, q=x94-1, and q+1=x94;
* the coordinate called y is the actual beta spacing plus one;
* the pair for schema a uses Y=x151-1;
* the pair for exponent x uses Z=x176+1;
* X=D+Z for every difference-coordinate Pell pair;
* the projected derived-label index is the affine restoration J printed
  in `../verification/P216_PORTS_AUDIT.json`, rather than an extra quantified coordinate.

The independent port audit checks all fourteen A*Y rows, all fourteen
Pell norm rows, all seventeen base/index/output triples, all three old
singleton modulus/congruence pairs and both old two-row pools. This
binds the theorem's semantic inputs to the literal parent coefficient
lists rather than trusting coordinate names alone.

## 3. Recovering the frame from retained rows

The final parent row basis has mixed the original frame with other
retained rows. Reading row129 alone as a sum-of-squares frame would be
incorrect. Reversing its 59 recorded integer row operations gives the
following exact identity, using original P216 row labels R_i:

    W-2-Σ_(36 atoms) atom²
      =22R4+R7-5R20+R21-R46+R129+R146.

No row on the right is deleted. Every actual base, index and output
occurs among the 36 explicitly reconstructed affine atoms. The horizon
row gives t=16+4d²>=16, so W>=258 and all required squares are strictly
less than W, before any exact-power recovery.

The actual canonical-index aggregate

    Σ_(14 pairs) [(X_i-1)²+(Y_i-k_i)²]-(A-1)Q

is likewise the following exact combination of retained rows:

    -22R4-R7+5R20-R21+R46-R129+R142-R146
      +R96+R104+R106+R108+R110+R112+R114
      +R116+R118+R120+R122+R124+R126+R128.

The fourteenth norm and all offsets are included. The actual cap,
comparison, anchor, index-residue and norm rows remain untouched. This
checks the literal hypotheses of the inherited canonical-index argument.
The aggregate alone is not claimed to prove canonicality without those
other retained hypotheses or the unbounded signed-Pell theorem.

## 4. An independent local proof of the large-A bound

The large center can be obtained directly from retained rows92--94.
Writing U=x136, V=x137 and the auxiliary frame coordinate as z0, those
rows give

    U=W(2z0-1), V=(W+1)U, A²+U²-V²=1.

Thus A²-W(W+2)U²=1. Since W>=258, U is nonzero and divisible by W.
The standard elementary solution theorem for the Pell equation at
parameter W+1 gives |A|=X_m(W+1), |U|=Y_m(W+1), m>=1.
The recurrence identity Y_m(W+1)=m modulo W gives W|m, hence m>=W.
Finally X_m(W+1)>=(W+1)^m>= (W+1)^W>W^W. This argument is independent
of all ten removed power rows and does not assume arithmetic signs that
are subsequently recovered from powers.

## 5. The sign bootstrap has no circular step

The new theorem initially recovers powers only at bases that happen to
be nonzero. This is enough:

1. t is already at least16. Its power gives F=t^t, an even positive
   integer at least2^64.
2. The retained equation B h_B=C+F+1 has odd right side, because C is
   even. Thus B is nonzero and odd. The retained H is2 modulo4 for
   every signed tuple, so BH is a nonunit.
3. The BH request gives x>=0 and q=(BH)^x. The odd beta multiplier
   gives |y|>=F, hence |1+(t+1)y|>1. The terminal endpoint excludes x=0.
4. Therefore q is a nonunit. Its request with index y+1 gives y+1>=0;
   the negative-y alternative would have y<=-F<-1, so y>=F>0.
5. The first endpoint excludes a negative initial quotient, and the
   terminal endpoint gives x>=2+(t+1)y. Consequently |q|>=2^x and q+1
   is a nonzero nonunit.
6. The remaining requests at q+1 are now exact. The inherited signed
   binomial digit recovery and local proof-flow decoding apply as in
   the parent.

The seven elementary bootstrap identities were independently recovered
from final row combinations avoiding every deleted row. Thus no claim
that B or q is already positive was needed to invoke the new theorem.

After this bootstrap all five bases are nonzero. Each old singleton
modulus is restored as T and its quotient as -δ/T. For each old pool,
restore L=E/T and K=2H+(2A-n)L. The divisibilities already proved make
these integers. This gives an actual old P216 zero, establishing the
needed new-to-parent implication. Conversely any parent zero supplies z.
This is an existential equivalence; the restorations are not polynomial
maps on arbitrary tuples.

## 6. Exact degree and literal artifact verification

The new residual has degree at most12. Its monomial

    x0² x4² x94⁴ x130 x178 x180²

in the reduced207-coordinate order has coefficient -2, independently
computed from the delivered DAG in a truncated polynomial ring. Thus
its degree is exactly12. All other residuals have degree at most2.
The final expression is structurally checked to be the sum of their
squares with the new residual square, so its degree is exactly24.
The nonzero homogeneous degree12 part has a nonzero square over Z;
the other degree4 summands cannot cancel it.

The separate verifier checks strict DAG syntax, integer constants,
coordinate ranges, backward-only references, every retained residual,
every declared semantic port, the entire six-term reciprocal expression
as an exact polynomial in already authenticated ports, the final sum of
squares, all207 used coordinates, and the leading coefficient. Deliberate
corruptions of a constant, A port, retained residual, final square and
degree certificate are rejected. It imports no builder or optimizer.

## 7. Baseline and novelty cautions

At commit315154b670d7, the incoming Pooled Projection archive already
has the216-variable quartic. The incoming Quotient Carriers archive has
a217-variable quartic with lower height, as well as12- and13-positive
variable equations with very large fixed coefficients. Report168 has
a215-variable degree10 reciprocal companion. These are distinct
comparison points; P207 does not dominate them in every metric.

The new mechanism reviewed here is a single base-weighted reciprocal
integer certificate across all five base groups, with zero-base tolerance
that permits replacing the initial bootstrap power certificates too.
The previous two-base reciprocal pool in report168 is related prior
work and should be credited. A global simplicity minimum or a
literature-wide priority claim is not established.

