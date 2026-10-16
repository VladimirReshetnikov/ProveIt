# Full-logic PSC compiler controls and removal of the exceptional-code gate

## Purpose

The equality-free 252-state experiment has a logical completeness defect at
the level of its isolated logical fragment. To measure a safer alternative,
these controls preserve every original logical schema, including the four
equality rows and the original (nondual) rho6. They also retain the original
base-4 formula constructors, Cantor proof/stack encoding, register layout,
and generalization-before-cache-read convention.

Only the nonlogical theory row changes. The old gated atomic membership and
equality vacuity bundle is emitted separately and retains its existing
`c != a,b` gates. The outputs remain uncalibrated compiler controls: the new
theory-to-calculus, enumeration and compiler bridges are not proved here.

## Exact theory rows

The fixed input/output labels are 0 and 1. The integer parameter c serves
both as a formula code and as the new hull-variable label. Write phi for the
matrix decoded from that code and use derived connectives relative to
`F=Rel(0,0)`.

    B(phi) = forall_0 exists_c forall_1
               (phi -> forall_0 (Rel(0,1) -> Rel(0,c))).

    Support(phi,c) = forall_1 (Rel(1,c) -> exists_0 phi).

    Closed(phi,c,seed) = forall_0
        ((seed(0,1) or Rel(0,c)) -> forall_1 (phi -> Rel(1,c))).

    PSC(phi,seed) = B(phi) -> forall_1 exists_c
                         (Closed(phi,c,seed) and Support(phi,c)).

For point PSC, `seed(0,1)` is the ordinary logical equality `Eq(0,1)`.
For subset PSC it is `forall_c (Rel(c,0) -> Rel(c,1))`. The use of c inside
the latter bounded subformula deliberately shadows the outer hull binder
only within that seed test. Its scope does not contain phi or the following
closure consequent.

The raw variants omit Extensionality entirely. This is a nonextensional
theory presentation using the complete logical equality subsystem; it is
not the defective logic obtained by deleting the equality rows.

## A safe simplification: the c>=2 gate is unnecessary for raw PSC

The earlier Extensionality-plus-PSC compiler emitted its new row only for
c>=2, ensuring that the dynamic hull label differs from 0 and 1. The raw
PSC row admits a better treatment of these two exceptions. This conclusion
applies to the raw row, not to the removed Extensionality conjunct.

Work in a nonempty ordinary structure satisfying irreflexivity. All derived
negations and existential quantifiers then have their ordinary meanings,
even when label 0 is bound. Decode code0 as Top and code1 as Rel(0,0).

**Lemma.** For both displayed seeds, the c=0 raw PSC instance is equivalent
to existence of a membership edge, and the c=1 instance is valid.

**Proof for c=0.** The matrix is Top and the hull binder collides with input
label0. In the bounding antecedent, the innermost subset test becomes

    forall_0 (Rel(0,1) -> Rel(0,0)).

Under irreflexivity, the whole bounding antecedent is therefore equivalent
to `forall y forall z not Rel(z,y)`: there is no membership edge anywhere.
If an edge exists, the PSC implication is true because its antecedent is
false. If no edge exists, every inner output requirement
`forall_1 (Top -> Rel(1,0))` is false, since the domain is nonempty.
For the point seed choose input0 equal to the current root1, making the
equality guard true. For the subset seed its subset guard is true for every
input, since every object is empty. Thus the closure conjunct is false in
both cases, and the PSC instance is false. This proves the equivalence.

**Proof for c=1.** The matrix Rel(0,0) is false uniformly by irreflexivity.
Every implication in the closure consequent therefore has a false
antecedent. The support clause's membership antecedent becomes Rel(1,1),
also false uniformly. The required closure/support conjunction is true,
so the instance is true. This also checks the potentially troublesome
capture of the output/hull label1.

ZFC proves irreflexivity and existence of a membership edge, for example
`empty in {empty}`. Consequently every exceptional raw PSC row is ZFC-valid.
Removing only the c>=2 theory gate is therefore safe for the intended
soundness direction. Schema coverage uses c>=2 matrices and is unaffected
by the additional valid rows. The separate logical vacuity gates must stay.

The script `check_exceptional_psc.py` independently evaluates the actual
binder syntax in all 69 irreflexive relations on domains of sizes1,2,3,
for both seeds and both exceptional codes: 276 cases. It confirms the exact
symbolic claims, including rejection of c0 in edgeless models. The proof
above, rather than finite testing, justifies the general result.

## Measured machine sizes

All figures count working states of the Wade public backend. The unique
missing terminal row can be totalized without adding a working state.
Sharing means the existing common-subsequence extraction runs before binary
lowering; each macro expansion is independently checked to be unchanged.

| Theory row | c>=2 gate | Without added sharing | With sharing |
|---|---:|---:|---:|
| Extensionality + point PSC | yes | 317 | 302 |
| Raw point PSC | yes | 294 | 284 |
| Raw subset PSC | yes | 297 | 288 |
| Raw point PSC | no | 285 | **276** |
| Raw subset PSC | no | 288 | **280** |

The unchanged original C/G program reconstructs in 281 states in this same
backend. Thus the ungated raw point/subset controls are respectively five
and one states smaller than that specific baseline, while retaining its
entire logical subsystem. These comparisons do not establish an improvement
over the independently optimized 253-state upstream machine: the backend,
initializer, interpreter and their verification costs must be accounted
for together.

The base4 theory-emission macro counts are76 for Extensionality+point PSC,
50 for raw point PSC, and56 for raw subset PSC. Formula savings do not
translate one-for-one into state savings because the backend shares helpers
and retains a62-state framework.

## Reproduction and trust boundary

Run:

    python measure_psc_controls.py --repo PROVEIT --output OUTPUT
    python check_exceptional_psc.py --output exceptional_psc.json

The scripts require the unchanged public vendor files pinned at
`297ab8df7e5de329605c3875b4934643b371a5e3`. Their expected hashes are verified
by the repository's existing recovery code before execution. All generated
tables and copied backend files are placed outside the source repository.

Optional `optimize_psc_orders.py` reorders the eight original logical rows
and one raw PSC row after GEN, retaining the final separate vacuity bundle.
It proves no new logical theorem; its symbolic interpreter checks all row
ASTs and the existing lowerer checks exact macro re-expansion. Its search
results are finite compiler-family measurements, never minimality bounds.

These controls have an additional emitted theory row compared with the old
C/G bundle format. The generic enumerator soundness invariant still has the
same form, but completeness extraction blocks must use the actual number
and order of pushed rows. The original source's fixed leaf-extraction counts
cannot be silently reused. No verified 276-state or280-state consistency
machine is asserted by this experiment.
