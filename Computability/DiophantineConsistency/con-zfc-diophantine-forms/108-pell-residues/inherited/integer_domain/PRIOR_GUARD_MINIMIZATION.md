# Guard compression by sign orbits and polynomial implications

This is a local, unconditional theorem about the two frozen signed-quotient
systems. It introduces no Turing-machine, number-theoretic, or consistency
assumption. The connection of the source system to syntactic ZFC refutation
remains the inherited direct-C222 arithmetic calibration. No assertion of
consistency and no new kernel-checked internal-ZFC proof is made.

## Exact results

| Core | All old guards | Reduced guards | Final variables | Quadratic rows | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|---:|---:|
| Affine | 1,228 | 645 | 4,879 | 3,150 | 4 | 22,910 | 127,285,349 |
| Retained wires | 1,228 | 661 | 7,058 | 5,297 | 4 | 24,277 | 1,992 |

The affine core has 2,944 coordinates and 2,505 rows. Among its coordinates,
1,228 are semantic natural inputs, 1,495 are natural arithmetic wires, and
221 are signed congruence quotients. The retained core has 5,075 coordinates
and 4,636 rows, with the same semantic inputs and signed quotients. The
arithmetic wire count is 3,626 in that core.

The compactness improvement changes the guards, not the core residuals.
Every old core coefficient and variable is retained verbatim. We append
only the selected nonnegativity certificates. Degree four is exact: a fresh
private guard variable has a nonzero fourth-power coefficient, and all
residuals are quadratic. The full collected expansions are supplied.

## The sign-orbit theorem

Let R_1,...,R_m be integer polynomials in coordinates X_1,...,X_n. A sign
vector e in F_2^n acts by X_i -> (-1)^(e_i) X_i. This is a diagonal
automorphism of the common zero set if, for each row, all nonzero monomials
of that row have the same parity against e. Indeed every monomial then
acquires the same sign, so R_j changes only to R_j or -R_j. The criterion is
checked by a finite exact parity calculation, including constant terms.

Suppose for each coordinate u in a set U there is such an automorphism
which flips u and no other semantic coordinate. These automorphisms commute.
For any integer zero, apply the u-automorphism exactly when its u-coordinate
is negative. Every coordinate in U is then nonnegative. Every other
semantic coordinate, and hence every selected semantic guard, is preserved.
The extra gate or signed-quotient coordinates may change signs, which is
permitted at this stage. The result is another zero of the same core.

There is no claim that the original zero already had nonnegative U-values.
The theorem establishes an existential equivalence by normalizing a zero
inside its sign orbit. Zero coordinates cause no problem.

For both frozen cores the parity equations have a 110-dimensional kernel.
The delivered certificate uses 110 generators, each flipping exactly one
semantic coordinate. They occur in two families, one pair per power graph:

1. Flip the auxiliary Z and the wire WZ. The defining product residual
   changes sign; every other occurrence of WZ is squared.
2. Flip the Pell coordinate U and the two signed quotients in the
   congruences B-A+U q=0 and S-X+U q'=0. These two products are unchanged,
   and U appears elsewhere only through U squared.

The proof relies on the exact row parity checks, not on these descriptive
names. The checker independently verifies every generator against every
core row. It also verifies that generators have distinct semantic pivots,
do not touch any guarded semantic coordinate, and do not flip another pivot.

## The ordered implication theorem

After sign normalization, assume the selected semantic guard coordinates
are nonnegative. We recover the remaining natural coordinates using a
finite ordered list of implications.

At one step an exact residual is rearranged as

    x A = B,

where x does not occur in A or B. The proof certificate establishes A>0
from previously proved lower bounds. If B>=0, then x>=0. If B>0, integrality
gives x>=1. If B-A>0, then x>1 and integrality gives x>=2.

Each asserted polynomial inequality is checked as follows. For a coordinate
with a previously established lower bound L in {0,1,2}, substitute
X=T+L with T>=0. Leave all other coordinates unchanged. Expand exactly over
the integers. Accept nonnegativity only when every coefficient is
nonnegative and every variable with an odd exponent in a monomial is known
nonnegative. An even power of an unrestricted integer is nonnegative. To
accept strict positivity, additionally require a positive constant term.
These are sufficient, not necessary, conditions. There is no numerical
sampling and no assumption on an unproved sign.

A useful cancellation example is

    B = 1 + 4Y q4.

Once B>=2 and Y>=1 have been proved, the factor 4Y is positive and B-1 is
positive. Therefore q4>=1, so no private nonnegativity representation for q4
is required. Other typical steps are A=2+a2, Y=k+yk, and V=Y^2(vd+1).
The guard on vd is retained where needed; the invalid branch vd=-1,V=0 is
not admitted by silently assuming V>0.

In the affine core, 645 guarded coordinates and 110 normalized pivots imply
the nonnegativity of all 2,723 natural coordinates in 2,382 recorded steps.
Exactly 473 formerly guarded semantic inputs are recovered by implications.
The 221 signed quotients receive no lower bound. The retained core uses
661 guards, 110 pivots, and 4,942 steps to recover all 4,854 natural
coordinates. Its 16 extra guards avoid depending on affine substitutions
that are absent from that literal core.

The reverse-greedy search producing the guard set is a heuristic, not a
minimality proof. The final finite implication certificate establishes the
claimed sufficiency independently of the search.

## Adding the selected guards

For each selected natural coordinate x, append the quadratic row

    x - a^2 - b^2 - c(c+1) = 0

with three private integer coordinates. Such a row forces x>=0, because
c(c+1)>=0 for every integer c. Conversely every natural x has this form.
Legendre's three-square theorem applies to 4x+1; it is not divisible by 4
and is 1 or 5 modulo 8. A three-square representation has exactly one odd
coordinate and two even coordinates. Write them as 2c+1,2a,2b, then subtract
1 and divide by 4.

Given a zero of the reduced-guard equation, normalize its sign orbit and
replay the bound implications. All original natural core coordinates now
have the required domain, so the signed-quotient source theorem applies.
Given a natural core zero, retain its coordinates and choose three-square
representations for the selected guards. This gives a zero of the new
integer equation. Thus the old and new equations have integer zeros
simultaneously. This is an existence equivalence, not a projection of every
raw zero into the natural source without normalization.

All arguments use integer ring identities, elementary inequalities, finite
linear algebra over F_2, and the three-square representation theorem.
They can be formalized in ZFC; no standard-model-only search or transfer
principle enters this local reduction. The complete internal coding of the
inherited source/refutation equivalence is a separate repository obligation.

## Reproduction

From the parent work directory, build and independently check the main form:

```sh
python3 guard_minimization/build.py
python3 guard_minimization/check.py
python3 -O guard_minimization/check.py
python3 guard_minimization/corruption_controls.py
```

The builder uses the stored optimizer output; the checker imports neither
the builder nor the optimizer. To reproduce the reverse-greedy search:

```sh
python3 guard_minimization/explore.py
```

The retained-wire companion uses the same theorem and checker:

```sh
python3 guard_minimization/build.py \
  --source signed_quotients/retained_candidate/equation.json \
  --optimization guard_minimization/retained_preliminary.json \
  --output guard_minimization/retained_candidate
python3 guard_minimization/check.py \
  --source signed_quotients/retained_candidate/equation.json \
  --candidate guard_minimization/retained_candidate
```

The supplied receipts are finite verification of universal algebraic
certificates and exact output files. They are not a search for a ZFC
refutation, evidence for Con(ZFC), or a proof of the inherited calibration.
