# Tagged Collection from the concrete full-seed source: author checkpoint

27 October 2026. Author: `/root/circuit_reduction`. Fresh final main and
Checks PASS. Independent review/replay is pending. No Git mutation or
accepted source modification was performed in this checkpoint.

The new files are
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedTaggedCollection222.lean`
(1226 lines) and `ValidatorSeedTaggedCollection222Checks.lean` (73 lines).
Their only direct prerequisites are accepted
`ZFCinPA.ValidatorSeedGuardedComprehension222` and `ZFCinPA.SetCongruence`;
Checks imports only the new main.

## Exact mathematical scope

For every arithmetic model of IΣ1, internally typed binary source matrix θ,
and arbitrary internal source terms a,t, `tagged_collection` constructs an
actual proof in `ValidatorFullSeedTheory222.seedTheory.internalize V` of

```text
Empty(t) → t∈a → ∃ C,
  t∈C ∧
  (∀ y, t∈y → y∈C → ∃ x, t∈x ∧ θ(y,x)) ∧
  (∀ x, t∈x → x∈a → (∃ y, t∈y ∧ θ(y,x)) →
    ∃ y, t∈y ∧ y∈C ∧ θ(y,x)).
```

The support input x is unrestricted by a. Only coverage uses x∈a.
Empty(t) and t∈a are source antecedents, not extra Lean assertions about
term codes or a selected model. All free parameters of θ,a,t survive the
opening/closing shifts. There is no distinct-code, standard-length,
fresh-label, raw CP/GIC, or supplied axiom-image premise.

The proof follows the actual construction in `KLowerTag.tag_collection`:
raw augmentation provides E, raw pairing gives r={E,t}, and the literal
full-seed matrix has root, empty, and singleton-input branches. The entire
member-closure and request pair is retained. It first gives E∈C and then
t∈C. Global support excludes outputs E and t. Coverage uses a singleton
of the given input and eliminates both exceptional branches.

The substantive arbitrary-matrix step is public
`matrix_second_transport`. It instantiates the existing all-internal
`SetCongruence.setReplace` at the unary substitution of θ and discharges
its actual equality-theory inclusion by the first component of seedTheory.
It does not identify source equality with Lean equality of variable codes.
Singleton uniqueness plus that source theorem transports θ(y,x′) to θ(y,x).

The endpoint includes `taggedCollectionProof` and
`taggedCollectionProof_isProof`, binding the selected actual internal proof
code to the complete literal conclusion. Three fixed total Σ1 graphs
construct the raw matrix, body and conclusion codes, with exact typed-value
identities. No Σ1 graph for the entire chosen proof-code map is asserted.

The source formula is arbitrary raw θ. Instantiating it with a represented
tagged interpretation, proving its marker-safe transport, and the actual
QHyp quotient/well-founded route remain separate. This packet proves no
raw GIC/CP image, ZF/ZFC interpretation, or new HA endpoint.

## Reading and validation

Before execution I read the complete initial main and Checks, the actual
semantic Collection construction, relevant full-seed/source-equality and
finite-context contracts, and the complete preparation/build drivers.
Every subsequent proof delta was read before the next compiler attempt.
The complete freezing driver was read before it executed.

Checks retain both source antecedents, coincident a/t labels, false and
true matrices, nested quantification, arbitrary free label p alongside
literal free label 0, exact unrestricted support, both binary-slot orders,
two shifts and opening, actual arbitrary-matrix equality transport, all
three raw graph instances, and the actual source `Proof` certificate.

Final fresh execution used Lean 4.32.0, `-M6000 -j1 -DElab.async=false`,
`LEAN_NUM_THREADS=1`, and a 512MiB free-space preflight guard. Both output
objects were newly written regular files in the private overlay:

`/tmp/validator-seed-tagged-collection222-author-3wmh9dnm/lib`.

The final main took 155.059s (2,065,024KiB maximum RSS); Checks took 2.940s
(1,926,860KiB). Main's log is empty; Checks has 13 axiom reports, each
containing only `propext`, `Classical.choice`, and `Quot.sound`. There are
no final warnings, new axioms, `sorry`, or `native_decide` declarations.

The exact approved closure is 207 cached current-source modules, of which
136 are Foundation, 615 selected cached object artifacts, and 45 explicit
external boundary primaries. Preparation reauthenticated all 2431 inherited
observations and all 660 actual first artifact providers. Execution records
2633 pre/post observations; freeze independently traversed every selected
source header, the reachable dependency DAG, all 252 first primaries, and
all 660 first artifact providers again. No Foundation or prerequisite
module was rebuilt. Existing provider qualifications, including historical
objects without additional companion artifacts, remain in the pinned
planning and cache records; no whole-closure fresh-build claim is made.

The accepted ROOT Guarded provider is selected directly. The four additional
SetCongruence-side clients retain their previously authenticated provider
records. No stale shared object was substituted or overwritten.

## Development history and frozen evidence

All four attempts, each with both exact source inputs, compiler driver,
command, logs, timing and pre/post pins, are preserved. Attempts 1–3 failed
normally in 188.206s, 203.074s and 165.468s. Repairs concerned existential
parentheses, explicit equality-symbol conversion, finite-context inference,
ambient-term/opening rewrites, finite propositional search depth, and raw
syntax code normalization. The final remaining goal was the literal
arithmetic numeral equality 2+1=3 inside a bound-variable code. No compiler
cap, imported prerequisite, or mathematical assumption was enlarged.

Frozen SHA256 pins:

| Artifact | SHA256 |
|---|---|
| Main source | `7a05c987d874b3a8c6d2457704c2c6017e40ca1121bb4e18924195887b692b7b` |
| Checks source | `18292749ebb6f158272423cb665766aa5520ab196afdc3a9e6b5798118efe24f` |
| Main object | `38d1ac2e6a4d133280457267cdb78f2bb401a413c680bd2b49569854b9d2557a` |
| Checks object | `a477459ca752fcdcb15ade446000221c19764071d379e2d2026ea42d2afe086b` |
| Cache inventory | `377db7c77dec3e9d1570419a08aa4cd23e8b7504d14d3f6153a9d582f27a22b0` |
| Replay summary | `0c06fbabf38086b3948a51d9af1396bceb5861e18d80dc240bc0a2d244d39aa4` |
| 57-file manifest | `000e1087c0b51722f70137f7f1d88ef36e29865a349ec7fe98b2aafab85f7ea9` |

The durable evidence is
`reviews/validator-seed-tagged-collection222-replay.json`,
`reviews/validator-seed-tagged-collection222-cache.json`, and the complete
`reviews/validator-seed-tagged-collection222-author-replay/` bundle.
The bundle includes the original frozen read-only plan, its auditor and
metadata-development records, all four compiler attempts, and final
reachable-closure/provider reauthentication. The original planning files
remain unchanged.
