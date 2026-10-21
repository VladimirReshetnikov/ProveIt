# A shifted-even codec matching the eleven-leaf inverse decoder

This is a mathematical calibration of a code algebra and inference rule.
It does not assert that a measured or verified smaller TM has been built.

## Constructors and the only overlap

Use Cantor pairing P and

```
I*(a,b) = max(0,4P(a,b)-2),   Q*(a,b) = 4P(a,b),
R(a,b)  = 4P(a,b)+1,          J(a,b)  = 4P(a,b)+3,
F = R(0,0) = 1,
N A = I*(A,F),    Ex_a A = N Q*(a,N A),
E'(a,b) = N J(a,b).
```

Interpret R as membership and J as disequality. Code zero is truth. The
only constructor overlap is

```
I*(0,0) = Q*(0,0) = 0.
```

Both equations have their required semantic meaning: truth implies truth,
and universally quantifying truth still yields truth. Do not describe
this change as a bijection on the old natural-number codes: the old
quantifier code for Q(0,0) and the old truth code now coincide.

Every positive code has strictly smaller fields. Indeed P(a,b) is at
least each field. If P is positive, `4P-2>P` and `4P>P`. R and J exceed
their fields even at P=0. Therefore a recursive interpretation of every
positive code is well founded, with zero handled by its truth clause.
For positive residues 0 and 2, the inverse constructor indices are h/4
and (h+2)/4 respectively. Every natural number is covered.

## Native theory calibration

Replace every numerical implication and quantifier constructor by I* and
Q*, and every equality occurrence by E'. Keep the literal structure of
the remaining rows and the seed/vacuity bundle. The public and private
labels remain natural numbers. In particular, the private binder is the
actual *new* code c of the matrix used in that instance.

All arithmetic freshness arguments survive the strictly-smaller-field
lemma. The helper label R(a,b) in G still exceeds both endpoints. The
algebraic proofs deriving equality logic and interpreting named formulas
use the displayed constructor equations, not a disjointness claim about
I and Q at zero. They consequently transfer to this new named-formula
encoding. This covers negative equality with the original rho6; its rho1
may be the full translated row or its proved compact equivalent.

It also covers the narrow dual-B variant proved in
`negative_equality_dual_b.md`: F is still literally R(0,0), rho3/rho5 still
give F-closure of membership, and the proof of F→Q_a F is unchanged.
That combination must retain the **full** translated rho1. No new
compact-rho1/dual-B equivalence is claimed.

For completeness, recompute `tau*(th(A))` using the new constructors.
There is no assertion that its numbers equal the old ones. The private
label remains absent from the decoded matrix by the strict field bound.
Complete222 already uses a twice-negated seed matrix. Since `N(0)=6`,
`N(N(0))=114`, and N is increasing, every such seed code is at least
114, so the old public roles 1 and 3 are distinct from the private label.
The named seed-to-K0 environment argument and K0-to-ZFC consistency
interpretation therefore apply with these recomputed numbers.

Soundness uses the ordinary ZFC model semantics just described; all odd
atoms are globally invalid under an assignment identifying their two
endpoints. Completeness gives a finite proof of F whenever ZFC is
inconsistent. Thus this directly calibrated native theory, with either
of the specified quantifier-row packages, is equiconsistent with ZFC.
It does not require equality of old and new theorem sets on their
untranslated numerical codes.

## The inverse decoder now matches both even constructors

Let

```
f(h) = floor(h/4) + [h mod 4 = 2],
d(h) = unP(f(h)).
```

For Q*(a,b), f returns P(a,b). For a positive I*(a,b), division by four
returns P(a,b)-1 and the residue-2 correction adds one. At P(a,b)=0,
both constructors are zero and f(0)=0. Consequently

```
d(I*(a,b)) = d(Q*(a,b)) = (a,b)
```

for all natural a,b. There is no requirement on odd inputs, by the
disequality/inverse-detachment corollary. The existing eleven-leaf loop
computing f therefore has exactly the required arithmetic interface
without its old two-decrement prefix.

Every ordinary MP step is included in this inverse inference, while its
extra quantifier steps preserve global validity and odd theorem premises
are impossible in ZFC models. The combined theory remains equiconsistent
with ZFC and supports the parity halt test. Concrete source construction,
global sharing, compilation, and unbounded machine simulation are still
separate obligations.
