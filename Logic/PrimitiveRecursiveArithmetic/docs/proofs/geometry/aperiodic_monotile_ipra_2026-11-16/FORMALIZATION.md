# Formalization plan

## Target libraries

Place the `lean/AperiodicMonotile` directory in the ProveIt Lake workspace and use:

- `ConciseIPRA` for syntax, `PRAAx`, `Prf`, and `pra_iff_native`;
- `IPRADerivations.Core.Pairing` for codes and simultaneous recursion;
- `Core.Search` and `Core.Pigeonhole` for bounded witnesses;
- `Core.Parity` and `Core.DescentEx` for the triangular-norm obstruction;
- `Core.Integers`, `Core.LinearAlgebra`, and `Core.Tactic` for affine identities.

## Milestones

### M1 — exact executable layer

Replace the `opaque` Boolean predicates in `Encoding.lean` with executable definitions.
Prove Boolean/specification equivalences for polygon simplicity, patch validity, window
coverage, and torus validity.

### M2 — closed hat and substitution data

Import the JSON constants as Lean lists or transcribe them with duplicated checks.  Prove
by `native_decide` or a small verified evaluator:

- the 13-vertex polygon is simple and has shoelace sum 32;
- the 29 placement rules have type counts `(10,1,8,10)`;
- the child selections yield the matrix in the report;
- every initial and step interface identity holds over rational axial coordinates.

### M3 — coherent growth

Flatten metatiles to elementary kite cells.  Build the finite adjacency/interface table.
Prove that the selected H child has one complete adjacency layer before the parent
boundary.  Inductively derive substitution depth `d(n) >= n-c0`.  A finite BFS in one
fundamental domain of the kite grid gives `Cgrid`, proving that level
`Cgrid*r+c0` covers the radius-`r` axial hexagon.

### M4 — finite torus reduction

Define bounded cross-section states for a strip modulo one period.  Instantiate the
existing finite pigeonhole theorem to repeat a slab and obtain a second independent
period.  Formalize the periodic alignment table as a finite graph transformation on the
torus.

### M5 — chevron/comet coupling

Implement the two exact contractions.  Count tile areas in a common fundamental domain
to get determinant `2/3`.  Split chevrons into rhombi, enumerate the three worm-cycle
families, synchronize their cycle lengths, and derive

```text
g (a * v_i) = (a/2) * v_i + b_i * v_i'
```

for `i=1,2,3`.  The sum relations imply `b_1=b_2=b_3`, hence `g` is a similarity.

### M6 — object-theory descent

Define `Q(m,n)=m*m+m*n+n*n` as a PR term.  Derive the four parity cases using
`Core.Parity`.  Instantiate `Core.DescentEx` to prove that

```text
Q(c,d) = 2 * Q(a,b)  ->  Q(a,b) = 0.
```

### M7 — assemble and transfer

Construct:

```lean
theorem einstein_hat_ipra :
  ([] : List (Fm PTm 0)) ⊢[PRAAx] einsteinHatSentence
```

and transfer it to the native scalar core with `pra_iff_native`.

## Recommended proof engineering

Keep geometry computational.  Avoid importing analytic real geometry into the object
theory.  Every affine fact needed here is equality or sign of a rational determinant.
Use Boolean reflection for closed local tables and reserve explicit derivations for the
uniform substitution, pigeonhole, strip-cycle, and descent arguments.
