# Even Pell indices: a direct 566-variable quartic for Con(ZFC)

The principal deliverable is the ordinary integer polynomial

    Q566(z_0,...,z_565) = sum(q_j(z)^2, j=1,...,372).

All 372 quadratic residuals are supplied in
`support8_default/equation.json`. All **6,431 nonzero monomials** of the
collected polynomial are separately supplied in
`support8_default/polynomial.json`. The polynomial has **566 unrestricted
integer variables**, attained degree **four**, and coefficient height
**2,445,790,974,704**.

The ordinary proof establishes that ZFC proves equivalence of the
absence of integer zeros and Con(ZFC). It composes the new transformations
with the explicitly pinned, previously reviewed direct C222 source theorem.
This branch uses neither a K215 coefficient encoding nor Jones's universal
polynomial. No new Lean/Rocq or sealed object-ZFC proof is claimed.

## What changes mathematically

First, seven pairs of scalar sign conditions are replaced by product
conditions. Their sums equal sums of retained nonnegative anchors, so
the original signs follow before any arithmetic interpretation. This
reduces the source from 75 to 68 predicates.

Second, each power request m=n^k is certified as m^2=n^(2k). Every Pell
seed therefore has an even prescribed index. A main ordinate of absolute
value one would force an odd auxiliary ordinate; its prescribed even
residue excludes this branch. Pell growth then supplies all needed index
lower bounds without separate index guards. Twelve more predicates are
removed, leaving 56. The common frame bounds the squared outputs. The
single derived t+1 pair takes two Pell steps, which is essential after
doubling the indices.

Soundness includes every sign of the shared auxiliary witnesses. Every
seed is oriented using a supporting call whose base is at least two.
Other calls allow base one. Completeness rebuilds fresh simultaneous Pell
certificates by an explicit finite-ring period and CRT construction.
It does not reuse auxiliary witnesses that satisfy the wrong source rows.

The original semantic front and the refutation/CRT controller remain
unchanged. The complete proof is in `proofs/even_power_compiler.md`; the
standalone parity lemmas and exact sign-sharing proof are alongside it.

## Exact comparison

| Complete equation | Integer variables | Quadratic residuals | Quartic monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Pinned direct parent | 604 | 372 | 9676 | 2445790974704 |
| Seven shared-sum pairs | 589 | 371 | 8157 | 2445790974704 |
| Even-index main result | **566** | **372** | **6431** | **2445790974704** |
| Lower-height alternative | 590 | 396 | 4776 | 964219 |
| Another height alternative | 597 | 403 | 4767 | 938267 |

The main result saves 38 integer variables and 3,245 collected monomials
against the pinned 604-variable direct equation at unchanged coefficient
height. It makes no global minimum claim. Smaller variable counts at
higher degree are separate tradeoffs elsewhere in the repository.

## Full finite specification

- `parent.json`: all 1,427 variables and 1,233 residuals before projection.
- `ledger.json`: all 60 intended body-row edits, 21 complete power-call
  interfaces, 15 seed interfaces, the corrected derived pair, the complete
  frame and all 56 predicates.
- `frame_parent.json` and `frame_projection.json`: 42 exact integral
  frame substitutions, applied before general projection.
- `support8_default/`: the main equation, its complete further inverse
  certificate and its collected polynomial.
- `support16_affine2/` and `support8_affine2/`: the two complete
  coefficient-height alternatives.
- `source/`: the unmodified pinned 75-predicate source, full raw metadata,
  inherited call/sign certificate and the seven-pair intermediate.
- `SOURCE.json`: exact repository paths, commit and source hashes.

Each projection restores every deleted coordinate uniquely as an integral
polynomial. No coordinate is discarded as unconstrained. The main result
has 861 such restorations across its two projection stages.

## Reproduce and independently verify

Only Python 3's standard library is required:

```sh
python3 build_even_index.py --check
python3 check_even_index.py
python3 -O check_even_index.py --output INDEPENDENT_CHECK_OPTIMIZED.json
```

The builder imports the unchanged, pinned projection engine. The separate
checker imports no builder, source emitter, theorem prover or optimizer.
It checks the whole source boundary, all 60 body edits, the seven sign
identities, the early output-sign ideal, all 643 semantic-prefix signs,
all power and seed polynomial interfaces, the frame, every projection
inverse and every coefficient of each final quartic. Targeted corruptions
restore an odd index, omit the required derived-pair correction or remove
frame doubling; the checker rejects all three.

`odd_index_negative_control.json` is a fully explicit **generic one-call
counterexample**, not a zero of the ZFC source. It satisfies the frame,
Pell equations and squared power condition at a spurious odd index.
Its even-index congruence fails. This documents why parity is essential;
it is not evidence for inconsistency or a search for ZFC refutations.

Finite checks bind the complete polynomials to the unbounded proof. They
do not replace that proof or re-establish the inherited C222/refutation
calibration by themselves. Source and proof dependencies are recorded
explicitly so the package can be incorporated into ProveIt.
