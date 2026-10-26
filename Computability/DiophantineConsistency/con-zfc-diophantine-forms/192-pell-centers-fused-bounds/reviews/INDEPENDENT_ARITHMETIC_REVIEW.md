# Independent arithmetic and exact-artifact cross-review

Prepared for the ProveIt research iteration of 25 October 2026. This is an
AI-assisted internal review by a separately assigned research agent, not
external human peer review.

## Review scope and verdict

The review covers three new ordinary arithmetic constructions and their
explicitly identified source interfaces:

1. The reciprocal fusion of the Pell cap and normalized-remainder budget,
   including composition with the linear orientation certificate.
2. The second-Pell-root carrier giving thirteen positive variables and its
   thirty-nine-integer domain translation.
3. The quartic-center growth replacement, its cofinal completeness proof,
   literal 212-coordinate graft, and reduced residual basis.

No unbounded proof gap, hidden sign assumption, or domain mismatch was found
in these new arguments. The compact construction's displayed leading-form
exponent was corrected from 98 to 99 during the review. All statements below
refer to the corrected version.

The historical native/C222/K215-to-ZFC calibration, canonical Pell
classification, binomial-CRT representation, and the normalized Pell
permutation theorem remain named inherited results. This review does not
claim a new complete Lean/Rocq build, an emitted object-language ZFC proof,
or a proof of consistency. Finite artifact checks establish exact identities
and dimensions; they do not replace the unbounded arithmetic proofs.

## 1. Reciprocal guard fusion

Reviewed inputs include `direct_work/guard_fusion/proofs/FUSION.md`, the
frozen `sources/anchor219.json`, the ordinary parent proof, source 157's
normalized-remainder estimates, and source 173's revised anchor construction.

### Soundness

For integers with U,V,R nonnegative and E at least one, put

    H=UV-UE-VR-1.

If H is nonnegative, U=0 would give H=-VR-1<0, and V=0 would give
H=-UE-1<0. Thus U,V are positive. The exact identities

    U(V-E)=VR+1+H,
    V(U-R)=UE+1+H

then imply V>E and U>R. These inequalities restore the two old
nonnegative guard gaps V-E and U-R-1.

The form G(a,b,c)=a^2+b^2+c(c+1) is nonnegative at every integer tuple
and represents every nonnegative integer. To prove surjectivity, apply
the three-square theorem to 4n+1; exactly one root is odd modulo four.
The two even roots and the odd root 2c+1 give the claimed representation.

Consequently a zero of the fused residual restores both old guard triples.
Their private-coordinate occurrence means no retained equation changes.
The source reconstruction is completed before invoking the cap's semantic
consequence. The proof therefore does not assume the Pell-index bound it
is trying to restore.

### Completeness

The canonical source construction supplies a positive even anchor C larger
than every other principal index, a positive Pell center A>W^W, C^2<W,
and thirteen other ordinates bounded above by Y_(C-1)(A). Thus

    E/V <= (W+13)/(2A-1)^2 < 1/2.

The ten actual normalized remainders obey r_j<Q/32, as follows from the
source 157 digit estimates and the source 173 anchor modification. Their
square budget is therefore R/U<5/128. Finally Q>=2 and Y_C(A)>=4 give
1/(UV)<=1/64. Hence

    E/V+R/U+1/(UV)<71/128<1.

This proves H>0 and supplies the fused ternary representation. This is
canonical-witness completeness, not a bijection between all old and new
zeros. That distinction is correctly stated in the proof.

### Composition with linear orientation

The composed soundness order is noncircular:

1. Restore the original cap and remainder inequalities from the fused guard.
2. Use the retained comparisons to bound the classified Pell indices.
3. Apply the linear orientation and power certificate to recover signs and
   requested indices.
4. Restore the calibrated original source.

The combined literal profiles inspected in the exact result ledger are:

| Integer variables | Exact degree | Residuals | Live binary operations |
|---:|---:|---:|---:|
| 106 | 32 | 47 | 1,830 |
| 82 | 16,964 | 23 | 1,723 |
| 81 | 2,097,732 | 22 | 1,711 |

The linear-orientation proof itself authenticates
Omega*=p+sum(Y-k)^2-sum(X) through the nonnegative small residue
sum(1-epsilon+(epsilon*nu-k)^2). It is an existential arithmetic
replacement under the inherited frame hypotheses, not equality of the
old and new polynomials on arbitrary tuples.

## 2. Thirteen-positive-variable Pell carrier

Reviewed inputs include `compact_work/new_carrier/PROOF.md`, the exact
incoming `CARRIER65_PROOF.md`, the uniform positive P66 theorem, and the
admissible942 source's complete outer-interface and canonical-completeness
section. The construction consistently uses the admissible942 tuple and
does not mix it with the indexed943 tuple.

### Odd-ordinate residue

The odd Pell subsequence satisfies

    psi_S(2j+1)=(-1)^j modulo 4S^2.

Its recurrence has coefficient 4S^2-2 and initial values 1,4S^2-1,
so the factor four is correct even when S is odd. For

    S^2 V^2-(S^2-1)y^2=1, S>=2,

Pell classification and divisibility of the abscissa by S force an odd
index. Hence y is +1 or -1 modulo 4S^2. The independently built
condition y=1 modulo four excludes the latter and yields 4S^2|y-1.
No already-decoded rank is needed in this deduction.

### Unit signs and recovered quotient

Cancellation of nonzero Delta leaves four integer factors with product one.
The consecutive-product negative-Pell obstruction excludes the negative
first factor; the remaining mod-four arguments exclude every other negative
unit. This occurs before any assertion about C, R, or B.

The carrier then proves h|B. If B were negative, positivity of m and
L>=|V| would force y>4|V|, contradicting the Pell bound |y|<2|V|.
Thus B>=0 and z=B/h+1 is a positive integer restoring the deleted parent
factor exactly.

For the companion L=bV, the b=0 case is correctly excluded first: it would
make an integer difference of squares strictly between zero and one.
The strong Pell equation gives f^2>c, so nonzero b and V have the same
sign and bV>=|V|. The same positivity proof therefore applies.

The soundness map replaces the parent's strong multiplier by hi and its
positive auxiliary ordinate by |y|. All remaining factors retain their
required values. The parent is invoked only after this reconstruction.

### Cofinal completeness

The canonical outer data are independent of the private strong seed.
A norm-one unit in the finite quotient ring supplies a positive Pell
ordinate I divisible by hc^2; positive powers provide cofinal choices.
The exact congruences for V*=chi_S(R)/S make the reconstructed T integral
and positive. Because the canonical rank is 3 modulo four, taking
y=-psi_S(R) gives y=1 modulo 4S^2. The reconstructed m is integral and
positive from B>0, h|B, L>=V, and |y|<2V.

The replacement of every positive input by 1+u^2+v^2+w(w+1) is a valid
surjective translation to unrestricted integers. It uses exactly three
integer coordinates per positive coordinate.

### Corrected leading form

With q0=beta J, k0=eta+zeta, the corrected main leading form is

    -128*q0^99*gamma*i^4*k0^15*w^14*s^27*f^8*T^4
       *(q0-F-alpha)^2.

The companion has f^4 in place of f^8 and the same q0 exponent 99.
The selected coefficient is -128*beta^99. The total degrees are 174
and 170. Their unrestricted-integer translations have degrees 348 and
340. The producer's exact leading-form check was rerun after correction.

## 3. Quartic-center growth replacement

The five-coordinate block is

    t=64+4z^2, S=t^2, T=S^2, Z=TF,
    X^2-Z^2-2ZF=1, F=T(2u+1).

All residuals are quadratic. It gives the Pell equation at a=T+1.
Because T|F and Y_n(a)=n modulo T, the positive classified index n is
a positive multiple of T, so n>=T=t^4. Therefore

    |F|>(2t^4)^(t^4-1).

Let d=2^19 and L=8^(d-1)t^d. For t>=64, t^3>=d/2 and
t^4-1>t(d/2-1). Moreover

    (2t^4)^(d/2-1)/L=t^(d-4)/2^((5d/2)-2)>1.

Thus |F|>L^t. Nonzero even F and |F|>t are established before its sign
is recovered by the inherited front bootstrap.

For completeness choose z divisible by 2^12, so
t=64 modulo 2^26, v2(t)=6, and v2(T)=24. Begin at index n0=T and
apply the inherited normalized Pell permutation theorem to select an
odd multiplier with F=2^24 modulo 2^ell, where ell>26 and t<2^ell.
Bit 24 of t is zero, so the binary supports of F and t are disjoint;
binom(F+t,t) is odd. The quotient F/T is odd, as required by the
literal divisibility row. All witness choices occur in the inherited
acyclic order.

Changing the horizon is a semantic cofinal-horizon replacement, not a
coordinatewise zero-set equivalence to t=16+4z^2. This distinction is
explicit in the construction and its certificate. The old proof needs
only the preserved lower bound, divisibility by four, and cofinality.

### Literal graft and horizon privacy

The source is the frozen principal210 equation with SHA-256

    20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a.

I read the producer, row-basis reducer, and independent verifier. The
verifier imports neither producer. It checks the pinned source, all
coordinate bindings, 146 literally retained rows, four replaced rows,
two added rows, complete expansions, and the reversible row-operation
ledger.

In both the original principal210 and new raw212 equations, coordinate
178, named `cofinal.horizon_root`, occurs only in row 125. Its old
residual is t-16-4z^2 and its new residual is t-64-4z^2. No other
residual or frame row contains this helper. Thus no hidden algebraic
use of the exact old horizon shape survives the graft.

The three old standalone growth witnesses are private as well:
coordinate 207 occurs only in row 148, coordinate 208 only in rows
147 and 148, and coordinate 209 only in row 149. Thus reinterpreting
coordinate 208 from tF to t^4F does not change any retained interface.

### Verified metrics and row basis

I ran `root_work/growth212/verify.py` both normally and with Python `-O`,
including corruption controls. Both runs passed and returned identical
mathematical results:

| Representation | Variables | Residuals | Exact degree | Monomials | Coefficient height | Residual height |
|---|---:|---:|---:|---:|---:|---:|
| Raw graft | 212 | 152 | 4 | 5,290 | 277,420 | 226 |
| Reduced residual basis | 212 | 152 | 4 | 21,556 | 6,432 | 60 |

The raw residual list has 1,003 monomials; the reduced list has 1,871.
The reduction consists of exactly 465 elementary operations
row_i <- row_i+k*row_j with i different from j and integral k. The
checker replays all operations forward and then replays the reversed
ledger with negated multiples. Both directions reproduce the exact
residual lists.

These operations preserve simultaneous vanishing of the residuals, hence
the integer zero set of their sum of squares. They do not assert equality
of the two expanded polynomials. Seven deliberately corrupted artifacts
were rejected, and 165 finite Pell recurrence fixtures passed. The latter
are transcription checks, not substitutes for the unbounded proof.

Actual review receipts are `GROWTH212_REVIEW_NORMAL.json` and
`GROWTH212_REVIEW_OPTIMIZED.json` alongside this note.

## Final review boundary

The three contributions prove explicit improvements or tradeoffs against
their inspected parent constructions. No global simplicity minimum or
literature-wide priority claim follows. Their mathematical claims compose
new ordinary arithmetic proofs with the identified inherited calibration;
the finite receipts establish exact artifact fidelity within that boundary.
