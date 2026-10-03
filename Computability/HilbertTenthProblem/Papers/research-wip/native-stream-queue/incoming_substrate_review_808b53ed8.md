# Seven incoming computational-substrate reports

The reports delivered at `808b53ed8` and `48ee077c7` pass mathematical review
within their stated domains and finite-certificate interfaces. All eleven
original verifier/CLI entry points replay successfully. Concrete input
contract defects were reproduced across three implementations; the accompanying
patches repair them without changing valid exported polynomials. Several
complete finite-certificate reductions are now proved and checked against
actual emitted equations. **The universal frontier remains 87 operations.**

This is a conventional proof and implementation review with exact finite
checks. It is not a proof-assistant verification, an exhaustive priority
audit, or a claim that finite tests prove the unbounded theorems. Original
archives are preserved. Repairs are distributed as patches against their
exact original bytes and replayed on private copies.

| Report | Reviewed result and boundary | Concrete outcome |
|---|---|---|
| Collision Geometry | Rational homogeneous chambers for a supplied finite signal schema; finite family unions | All author checks pass; redundant inequalities and private slacks can be removed in five exported packets |
| Signal Machine Certificates | Complete simultaneous-event chronology, fixed schema and externally fixed horizon/normalization | Delete endpoint identities and implied initial-order checks; two-signal example 6 rows/5 witnesses becomes 4/4 |
| Maximal Parallel | Quadratic natural certificates for resource-maximal rounds and horizon-indexed histories | Repair mutable network inputs and inconsistent guard polarity; valid formulas unchanged |
| Order Is Not a Moment | Exact ternary word-profile intervals, special two-marker quartic and supplied-multiplicity Heisenberg slices | Save 8 finalizer multiplications while preserving real-orthant nonnegativity, or 10 for natural-domain equivalence |
| Exact Convergence | Exact finite attainment of a known limit in a fixed stochastic game; bounded trajectory certificates | Repair an independent-checker input bypass and an integer-scale loader path that used floating point |
| Total Quadratic Semantics | Unique final labels and first activation times for a fixed finite irreversible catalogue | Repair deep input ownership and aliased exports; the finite catalogue does not provide an unbounded universal history encoding |
| Affine Matrix Inputs | All-dimensional finite-or-periodic obstruction for one affine ordinary input; prior quadratic loader and existential cyclic-block compiler | Square gates lose one 3-dimensional block and one added coordinate; worked example dimension 20→17, added coordinates 6→5 |

Read the detailed reviews for the proofs, domains, examples, references and
independent checks:

- [Both signal reports](incoming_signal_review_808b.md).
- [Maximal parallelism and exact order](incoming_parallel_order_review_808b.md).
- [Exact convergence and irreversible semantics](incoming_convergence_review_808b.md).
- [Affine matrices and the square-block projection](affine_matrix_square_projection_review808b.md).

## Reproduced defects and repairs

**Parallel network ownership.** Construct a round from consumption `[[1]]`
and production `[[0]]`, and its zero for input 1 and firing count 1. Mutating
the accepted consumption list to `[[2]]` leaves the compiled polynomial zero
but changes the exported network and makes the firing illegal. The repair
takes immutable nested snapshots of matrices and guard conjunctions.

**Parallel guard polarity.** `Atom(0,1,2)` is accepted by the original code.
The semantic oracle compares a Boolean with 2, but the compiler takes its
truthy branch. A true-guard witness therefore zeros a polynomial whose own
semantic oracle rejects it. The repair enforces exact natural species and
threshold values and an exact Boolean polarity. Both fixes are in
[maximal_parallel_immutable_guards.patch](maximal_parallel_immutable_guards.patch).

**Bellman input binding.** Start with a one-step equality certificate for
two identity rows and initial payoffs `(0,0)`. Alter only the declared input
numerators and the supplied game's initial payoffs to `(1,0)`. The old checker
still reports a zero and successful independent game verification, because
it iterates from a separate, unbound scaled initial vector. The actual
discounted endpoint is `(1/2,0)`, which fails the equality condition.
[exact_convergence_input_binding.patch](exact_convergence_input_binding.patch)
binds the input vector, denominator, witness scale, reward, discount, endpoint
mode and supplied game, and checks exact scalar/index domains. It retains
the generator's rational scaling convention and all valid delivered examples.

**Bellman optional loader scale.** Passing integer `scale=1` to the source
program's reciprocal-power encoding uses Python floating division. Counter
1075 becomes `0.0`, while the default rational scale gives the required
nonzero `2^-1075`. [exact_convergence_integer_scale.patch](exact_convergence_integer_scale.patch)
normalizes exact integer or rational scales before division and rejects
floating-point and Boolean scales. The default loader and supplied exports
were already exact; their values are unchanged.

**Irreversible network ownership.** Compile a seed `(0,1)` and a rule activating
label 1 at site 1. Mutate the accepted seed list to `(0,2)`. The original
polynomial still accepts its old zero, while its current network has a
different inactive-site outcome. Exported coordinate arrays also alias the
compiler's internal arrays. [total_quadratic_immutable_inputs.patch](total_quadratic_immutable_inputs.patch)
owns nested rule/seed/network values, copies exported containers and rejects
inexact natural coordinates and options. The original also accepts a fractional
seed label `1.5` outside its declared alphabet; the same exact-type validation
rejects it. Valid polynomial coefficients and
example exports remain unchanged.

These are boundary defects in implementations, not counterexamples to the
theorems with fixed exact input data. The patches do not claim to protect
deliberate mutation of every public compiler object or fabricated low-level
polynomial descriptors. Source hashes and exact constructors remain part of
the replay contract.

## Verified reductions and what they cost

The sparse signal compiler's same-birth equality rows are identically zero;
same-death gap rows are differences of two retained flight rows. Delete both
classes. If the schema has a positive number of batches or certifies halting,
retained natural strict-lifetime gaps imply strictly ordered integer input
positions. The separate input-order slack is then uniquely restored as
`next_position-position-1`. A zero-batch prefix must retain those input checks.
This gives `R_new=R_old-(I-E)-Z_birth-J` and `W_new=W_old-J`, with the meanings
and complete proof in the signal review. Its rational counterexample explains
why the slack projection needs integer inputs.

The order quartic has eight residuals that are products of natural coordinates.
Leave them unsquared while retaining the other sixteen squares. All summands
remain nonnegative on the real nonnegative orthant, and their complete zero
set is unchanged. If only natural inputs are required, the two parity
residuals `e(e-1)` may also remain unsquared. These variants save exactly 8 or
10 finalizer multiplications in a schedule retaining the same residual
evaluations; they are not optimized total circuit counts. Both full sparse
polynomial correction identities are checked. A supplied rational fixture
gives value `-1/4` for the ten-term reduction, so its positivity scope is
strictly weaker. The 24 coordinates and natural witness uniqueness remain.

For an affine-matrix square gate `z=x²`, substitute `u=2z-x` and replace
`T(2x,u),T(0,u-2z+x)` by `T(2x,2z-x)`. This gives a complete integer zero-set
bijection and a full sum-of-squares identity on the restoration graph. With
`g` multiplication gates, of which `s` are squares, dimension is
`6g-3s+2`, added coordinates `2g-s`, and residual count `2g-s+1`.
Degree remains at most four. General affine operand evaluation and matrix
word certification still need to be charged before any universal comparison.

All these transformations concern complete supplied finite polynomials.
None pays for an unbounded chronological selector, an arbitrary fixed-length
machine-table loader, or a fixed-arity universal computation certificate.
The 87-operation universal construction and the separate 744-operation GPCP
route retain their existing status.

## Reproduction and provenance

Run from any working directory, with Python and SymPy available:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_808b53ed8.py
```

From outside the repository, supply the absolute path to that script. It
compares a fresh run with the committed receipt; `--write` explicitly updates
the receipt. Assertions must remain enabled. It verifies all archive hashes,
rejects unsafe ZIP members, checks recovery of all seven archives with
`git show` at their arrival commits, replays all eleven original entry points
in private copies, and runs the independent proof-oriented checks and repairs.
The [receipt](incoming_substrate_review_808b53ed8.json) records every original
member hash and every helper's source hash, source-derived counts, reproduced
defects, patch hashes and unchanged valid outputs.

Only top-level author receipt fields named `python`, `python_version`,
`runtime_seconds` or `elapsed_seconds` are ignored for semantic comparisons.
Mathematical counts, coefficients, domains, witnesses and source digests are
retained. CLI-only helpers execute in separate processes; imported helpers
restore their temporary module names. Every patch is applied to a private
copy and its resulting source bytes are verified before execution.

The larger context is the [preceding six-report review](incoming_substrate_review_1977e6ea6.md)
and [earlier three-report review](incoming_substrate_review_6914ccca6.md).
`Waterfall_Diophantine_Certificates.zip`, delivered at `24a743255` while this
batch was being reviewed, was initially [triaged](waterfall_intake_triage_24a743255.md)
and is now [fully reviewed](waterfall_report_review_24a743255.md), with all eight
author commands replayed and a complete forced-boundary reduction. The original
triage preserves its more limited historical read scope.
