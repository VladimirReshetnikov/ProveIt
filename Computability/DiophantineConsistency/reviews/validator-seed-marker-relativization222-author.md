# Moving-marker internal source derivation transport: author checkpoint

27 October 2026. Author: `/root/circuit_reduction`. The new main and Checks
are frozen after a fresh private PASS. Independent review/replay remains
pending. No accepted source, dependency object, shared documentation or Git
state was modified by this checkpoint.

The source files are
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedMarkerRelativization222.lean`
(331 lines) and `ValidatorSeedMarkerRelativization222Checks.lean` (60 lines).
The main imports only accepted `ValidatorSeedMarkerDischarge222`; Checks
imports only this main. Collection is not imported or used.

## Exact statement and boundary

For a source set theory T with its actual Δ₁ recognizer, and every
arithmetic model V of IΣ1, let

```text
D_j       = member(fvar j, bvar 0)
R_j(p)    = relativize(D_j,p)
Q_j(s)    = {¬Empty(fvar j)} ∪ relSet(D_j,s) ∪ domSet(D_j,j).
```

The new `AxiomImages T V` is exactly the remaining source axiom obligation:
for all internal p,j, `IsFormula p`, `p∈T.Δ₁Class` and `p<j` imply an actual
seedTheory derivation of `{R_j(p), ¬Empty(fvar j)} ∪ domSet(D_j,j)`.
It is not replaced by a model-validity, Good, proof-transform or standard
quotation assumption.

Under precisely this boundary, `derivable_tagged_bounded` proves all ten
actual internally coded derivation cases with the bounded Σ₁ motive

```text
Derivation T der → ∀ j≤B, der<j → der+j≤B →
  Derivable seedTheory (Q_j(fstIdx der)).
```

The generic model may be nonstandard; contexts, proof codes and counters
are internal elements of V. Actual `ISigma1.sigma1_order_induction` handles
the proof code. The bounded counter quantifier and Δ₁ antecedents keep the
motive Σ₁. There is no induction over a standard list of proof nodes.

The ALL child uses j+1 and its actual smaller code; the budget follows from
`child+1≤parent`. SHIFT uses the predecessor k of j=k+1, with parent<j
implying child<k. The source term language has no function symbols: the
existing typed `term_is_fvar` yields the raw-code adapter. In EXS its actual
coding inequalities give `i < code(fvar i) < parent < j`. Thus the required
negative domain formula is genuinely in `domSet(D_j,j)`.

The new family law is
`shift(R_j(p)) = R_(j+1)(shift p)`, not shift-fixedness of a free marker.
It is proved by actual eight-case internally coded formula induction.
Opening, substitution, negation, sequent insertion and sequent shifts are
bound to the same family. The ALL sequent law supplies exactly the extra
`free(¬D_j)` side formula, which participates in its disjunction proof.

Choosing B=der+j removes the auxiliary budget at the public derivation
endpoint. For a refutation, j=der+1 reduces the transformed singleton
falsum sequent to the accepted MarkerDischarge residual. That existing
source proof discharges the side set and empty-marker guard. Consequently
`provable_falsum_of_tagged` constructs an actual seedTheory refutation.
With explicit IΣ2, `refutation_witness` composes the already proved seed
interpreter to obtain `∃ d, ArithmeticHistory222.value d=2`.

The hAx obligation remains explicit in both endpoints. This packet does
not discharge tagged source axiom images, identify raw membership with a
quotient relation, construct QHyp/WF models, or prove a ZF/ZFC or new HA
consistency equivalence. Those are subsequent obligations.

## Reading and checks

I read the full main and Checks before execution, all subsequent deltas,
and the complete preparation/build/freezing drivers before their relevant
execution. Source review included the actual ten Foundation derivation
constructors, internal code decreases, typed term classification, formula
shift/free/substitution contracts, canonical domain side sets and accepted
marker residual/source refutation contracts. I authored several earlier
source/seed prerequisites; this is an author checkpoint, not an independent
review of those dependencies.

Checks cover arbitrary internally typed formula and term codes, nested
ALL/EXS with arbitrary parameters, exact opening and shifted side sets,
EXS variable bounds, the ALL budget, SHIFT predecessor, the unfolded hAx
resource, the zero-marker falsum residual and the actual value-2 endpoint.
Fifteen axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. These are Lean metatheory axioms, not added source-theory
axioms. There are no placeholders, native_decide or new axiom declarations.

## Build and provenance

The final pair passed with Lean 4.32.0,
`-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, and a 512MiB free-space
guard. Main took 17.634s with maximum RSS 1,958,016KiB; Checks took 2.413s
with maximum RSS 1,915,732KiB. Main's log is empty and Checks has only the
15 expected reports. Fresh regular output objects are under

`/tmp/validator-seed-marker-relativization222-author-scwpqslx/attempts/1793102312940420091/lib`.

Exactly 203 current-source cached modules, including 136 Foundation
modules, were reused: 611 cached artifacts and 45 explicit external
boundary primaries. Final reauthentication traversed every source header
and reachable dependency, including `public meta import Aesop`, and checked
all 656 actual first artifact providers (248 primary module providers).
No prerequisite or Foundation module was rebuilt. The accepted Marker
peer provider is selected directly. Historical provider qualifications,
including absent companion artifacts where recorded, remain explicit in
the unchanged approved plan and cache inventory; this is not a fresh
whole-closure claim.

The frozen closure reauthentication contains 19,075 observations, including
repeated pre/post observations. All compiler commands, environment paths,
source snapshots, input inventories, logs, timing, object hashes and
source/provider checks are retained. The original approved read-only plan,
auditor and manifest are copied unchanged into the evidence bundle.

All three attempts are preserved. Attempt 1 stopped before proof
elaboration in 0.184s because Lean resolved the new namespace directory
before the separate cached namespace directory. The private driver was
corrected to place approved cache symlinks beside each attempt's fresh
outputs. No accepted object was overwritten. Attempt 2 failed normally in
16.220s: an explicit formula-code argument was missing from the induction
application, and the actual history value needed its full namespace.
One unused simp argument was also removed. Attempt 3 is the clean final
pair above. No import, cap or mathematical premise was enlarged.

## Frozen pins

| Artifact | SHA256 |
|---|---|
| Main source | `b40439c7e0613da8c19bba3396fcf14314c3480cfcd49aafdeb3cc27cbb6a7a2` |
| Checks source | `d75d002868515cf50761b8af464dbb1f85e03be47bd003962d78511b5ed1da6d` |
| Main object | `ae948ce1d79920d219dee0cb6b19074ec6e5b23e2bcf2b6d5ac8c473d0906669` |
| Checks object | `15b22d6f904dbe7382a9a63566593bee9ac062e028e28c5daccf6e1a29a11e8e` |
| Cache inventory | `b14cd8e3be37fec2fb7acc7fd03a6d161abaca0d8099ab39a022fd33b748b470` |
| Replay summary | `6a9f41af0b6c3683f1ae0f2c6f1767f480e31a98845e8e6e6b9784072a65e5d1` |
| 35-file manifest | `dfae5f31c78551391992f9e6af0b35dfb1bbb7a568cb6d9bd62bbea4a4085130` |

Durable evidence is `reviews/validator-seed-marker-relativization222-replay.json`,
`reviews/validator-seed-marker-relativization222-cache.json`, and the complete
`reviews/validator-seed-marker-relativization222-author-replay/` bundle.
