# Paid target-selector fusion in both complete U21 sources

The [complete arrays and receipt](residue_affine_sparse_target_fusion.json)
cost **465=170M+295A** for the one-program interface and
**464=170M+294A** for the two-program interface. Each saves one
multiplication from its own [prime-recenter parent](residue_affine_sparse_prime_recenter.md).
The 67 strictly positive witnesses, all state codes, and degree upper
bounds **5091** and **5160** are unchanged.

Every new full polynomial is identical to its own parent over every
commutative ring at the same supplied coordinates. This is a source
identity, so the inherited positive-zero theorem needs no new witness
selection or chronology argument. No arithmetic minimum or improvement
to the universal84 bound is claimed.

## 1. A paid coefficient collision

Write `E_i=edgei_hat−1`, and use the actual existing wires

    e = edge_29,
    A = prime_selector_112 = E5+E8+E9+E14,
    J = selectors_70 = sum_{i=0}^{35} E_i,
    J7 = u21_grouped_J_7 = J−E29.

The defining parent row is literally `J=J7+e`. All four wires are already
live in the retained noncontrol source. The parent target word has the
three contributions

    6e + 7A + J.

They can be computed instead as

    7(A+e) + J7,                                      (1)

because `J=J7+e`. Two coefficient multiplications become one. Forming
`A+e` adds one addition, while joining the formerly separate `6e` term
removes one addition. The net saving is exactly **one multiplication**.
The scalar 7 use remains paid; no coefficient multiplication is treated
as free.

## 2. Minimal edit and full-source proof

The [fresh helper](residue_affine_sparse_target_fusion.py) authenticates
both complete parent arrays and guards these literal rows:

    joint_34 = 6 * edge_29
    joint_46 = joint_45 + joint_34
    joint_35 = 7 * prime_selector_112
    joint_47 = joint_46 + joint_35
    joint_56 = joint_55 + selectors_70.

Only `joint_46` consumes `joint_34`; only `joint_47` consumes
`joint_46`. The new array deletes those two private rows, inserts

    target_seven_group = prime_selector_112 + edge_29,

and changes exactly three retained definitions:

    joint_35 = 7 * target_seven_group
    joint_47 = joint_45 + joint_35
    joint_56 = joint_55 + u21_grouped_J_7.

Every other retained row is literal. The new group is placed before its
multiplication, and all its inputs are previously paid. Complete
topological and backward-liveness checks cover both emitted arrays.

The new `joint_35` exceeds the old value by `7E29`. Each new value from
`joint_47` through `joint_55` exceeds its old value by `E29`. At
`joint_56`, replacing `J` by `J7` cancels that difference. Thus
`joint_56`, target word `joint_61`, current word `joint_24`, and all
subsequent consumers have their exact parent values. These ten named
registers are the entire list of unequal retained computed values;
454 retained computed values in the one-program source and 453 in the
two-program source are equal.

The helper independently expands each full current and target word into
all 36 actual supplied edge hats, including the constant term from
`E_i=edgei_hat−1`. It checks every coefficient against the unchanged
literal 36-edge source/target table and code list. It also verifies each
of the ten intermediate differences above by exact integer polynomial
expansion.

A second complete interpretation interns exact expression tuples and
normalizes all globally affine expressions over the entire supplied-port
basis. It uses exact dictionary keys, not equality of expression hashes.
Actual old and new output IDs coincide, and all cuts used for the
finalizer proof are bound to equal values computed by those full arrays.
The literal finalizer expands to

    U * (1 + r0² + r1² + r2² + r3² + r4² + r5²) − 1,

with `U=sparse_all_units` and the six actual `norm_residual` values.
All 72 native rows and all 20 comparison/finalizer rows are unchanged.
Consequently the proof establishes the whole polynomial identity, not
just equality of a target coefficient vector or a digest of a cut.

## 3. Complete paid ledgers

The current word still costs `23=9M+14A`. The target word decreases
from `37=12M+25A` to `36=11M+25A`. Their paid shared register is still
`joint_12=29*control_codes__duplicate_state_2`. Their live union now
costs `58=19M+39A`. The further control producers `B*N`, `14P` and
`C+14P` cost another `2M+1A`; the comparison subtraction is included in
the finalizer stage below.

| Disjoint stage | One program: M,A,total | Two programs: M,A,total |
|---|---|---|
| Retained noncontrol base, including five residual producers |142,247,389|142,246,388|
| Private control producers |21,40,61|21,40,61|
| Remaining finalizer |7,8,15|7,8,15|
| Complete source |**170,295,465**|**170,294,464**|

All 929 emitted rows and every supplied port are live. Excluding all
20 comparison/finalizer rows gives certificate costs
`445=163M+282A` and `444=163M+281A`, with seven comparisons and
67 positive witnesses in the inherited convention. The headline counts
include every comparison and finalizer operation.

The state codes remain exactly

    0,1,15,21,9,17,13,11,5,18,8,38,30,32,10,3,12,4,40,2,6,7,14.

They are injective, with loader code 0, halt code 14 and maximum 40.
The one-program interface retains the inherited fixed program
`E=3^e`, ordinary positive input `x`, positive height slack `eta`,
`h=E+x+eta` and `B=64h>=192`. It has 69 supplied ports.
The two-program interface retains fixed `E=3^e` and fixed dyadic
`C>=64` with `C>E`, `h=x+eta` and `B=Ch>=128`. It has 70 supplied
ports. Both retain the same 67 positive witnesses. The literal
height/radix definitions and the entire 389/388-row noncontrol bases
are checked against their respective parents.

The two arrays still differ only by deletion of `height_83` and the
two inherited height/radix definitions. This source correspondence is
not a claim that the two interfaces have the same positive zero set.
Each full zero-set identity is to its own immediate parent, with its
own fixed-program conditions, ordinary-input meaning, payload, native
bootstrap and chronology. No new assertion concerns invalid fixed
parameter slices.

## 4. Degree and finite validation

Full polynomial identity already transfers the inherited degree upper
bounds. The helper also freshly expands the actual native main norm as

    (X+ac+G)² − (a²+4a+3)c²
      = X² + 2acX + 2GX + 2acG + G² − 4ac² − 3c².

Its actual computed boundary degrees give norm bounds 816 and 827;
propagation through the literal native product gives 4993 and 5062,
and the outer SOS contributes at most 98. The complete upper bounds
are 5091 and 5160. Naive gatewise propagation would instead give
5157 and 5227, because it misses that cancellation. No exact-degree
claim is made.

The receipt records both entire sources, all row/consumer guards,
exact affine vectors and intermediate differences, the whole-source
identity, finalizer contraction, liveness, complete ledgers and degree
checks. An additional 64 signed modular whole-source comparisons vary
every supplied port and check all equal retained values. These samples
are diagnostic support, not the proof of any identity.

The candidate came from a finite whole-target basis search that included
paid remainder sums and current-word values. The selected replacement
of `J` by `J7` exposes the common coefficient 7. The separate scratch
search is not a global optimum certificate and is not needed to replay
this exact selected transformation.

All three immediate-parent files are authenticated and read only as
inert bytes or JSON:

| File | SHA256 |
|---|---|
| `residue_affine_sparse_prime_recenter.py` | `c5d8b2690f1e2a9b50aa063a95f81297ff388b276ab83ce487aa4cbaacc46798` |
| `residue_affine_sparse_prime_recenter.json` | `e35399b892850ace2bf860fd37f0e3e9f8af34dd8e516f66718547e0689fe26c` |
| `residue_affine_sparse_prime_recenter.md` | `78e81a12145ecf2b5b57fecdbef614cafa2a96ff0b86e488c4479546914c108c` |

No predecessor helper was executed or imported. The fresh helper uses
only the standard library, checks the parent's helper/array bindings
and preserves its canonical in-memory data. Duplicate JSON keys and
noninteger numeric tokens are rejected. Explicit checks remain active
under `-O`; receipt creation is exclusive and replay compares exact,
type-sensitive canonical JSON.

Fresh normal and optimized exact replays from `/` both passed:

```text
python3 /tmp/residue_affine_sparse_target_fusion.py --root ABS_WIP --expect /tmp/residue_affine_sparse_target_fusion.json
python3 -O /tmp/residue_affine_sparse_target_fusion.py --root ABS_WIP --expect /tmp/residue_affine_sparse_target_fusion.json
```

Helper SHA256: `256892e0f2431d150dd059d55cbdf58bb2d44dd45e9bfe723faf6ed262b9fd2f`.
Receipt SHA256: `5b94b171976f73b6bfedb6b068fb145652c8c62e79d6ef8103d9a5da393ae855`.
