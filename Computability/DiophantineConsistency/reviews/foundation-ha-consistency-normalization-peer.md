# Fixed HA consistency normalization: independent review

26 October 2026. **PASS; no findings or source changes requested.**

I read the full 76-line main, 41-line checks, author receipt, complete author
driver, and the exact source interfaces for the fixed provability predicate,
its Σ₁ certificate, empty-environment syntax interpretation, and accepted
negation and hierarchy proof composition. I independently reauthenticated
the selected closure and freshly compiled both leaves in a separate private
overlay. Both compiled on the first attempt and both output objects are
byte-identical to the author's.

Root authored this new pair. I authored the preceding read-only proposal
and several reused HA/syntax/hierarchy leaves, including the Σ₁ comparison.
This is an independent review and replay of Root's composition, not an
independent reimplementation or fresh replay of all prerequisites.

## Exact source and proof scope

Main `FoundationHAConsistencyNormalization.lean` SHA256:
`1a69a875738db6ebbd7c5e466022d0d169ee747e50184fc838077d42f0ad8e09`.
Checks SHA256:
`33a40c1e041f77f52fee8d6fbfecffadee7eaf567436daffb4a78f5382722326`.

The proof compares `FoundationZFCConsistencyNat.ggConsistency` with
`HA.neg (ordinaryAux Fin.elim0 Empty.elim rho)`, where `rho` is the actual
Foundation ZFC provability predicate at falsity. The theory includes choice.
`source_eq_neg_rho` is literal `rfl`, retaining the actual theory and coding
instance. `rho_sigma_one` obtains the real hierarchy certificate from
`provabilityPred'.sigma_prop` and its exact value equality. It does not
pretend the proof predicate is DeltaZero or assume an HA decision procedure
for an independently chosen checker.

`sentence_empty_env` unfolds only the accepted syntax maps, applies the
capture-avoiding rewriting theorem, and identifies the two empty-domain
environments by empty elimination. The nested universal/existential check
exercises that equality. This step is syntactic and does not appeal to
standard-natural semantics or formula extensionality through models.

The accepted actual Σ₁ proof yields `GG rho ↔ ¬¬ ordinary rho` inside HA.
Its public negation comparison gives `¬GG rho ↔ ¬ordinary rho` without
extracting a positive witness. The accepted `translated_neg rho` supplies
`¬GG rho ↔ GG (∼rho)`. The two composition directions in `equivalence` have
the correct orientation. Both implication projections and finite-context
weakening are genuine `HA.Proves`/`HA.Relative` derivations. There is no
source PA-equivalence premise, consistency assumption, new HA rule,
positive Σ₁ DNE, Markov rule, or unbounded DNS.

In particular, the code never equates the ordinary interpretation of NNF
source negation with HA negation of the ordinary positive predicate. This
packet does not prove an HA comparison with the independent BProv/C222/C254
checker, the current Diophantine sentence, a syntactic `Formula.Sentence`
free-variable certificate for the new target, or its standard-Nat semantics.
Those claims remain separately scoped.

## Independent authentication and replay

The frozen author summary is
`foundation-ha-consistency-normalization-replay.json`, SHA256
`292e1cfff7fb291103d7127fce2fffca8f023bab5e39640d756e2aeb834c736a`;
its nine-member manifest is
`fca8110bfa4838b476f9da53e10b10f9bd25682e8c4427e3608e2ccc4420b268`.
I read the complete author driver before execution and separately used a
reviewed independent replay driver with a nested-comment-aware import
parser. All 455 cached source/import records were rechecked; the exact
dependency traversal reaches all and only those modules and all 57 explicit
external boundaries. No cached client imports either fresh leaf. There
were no import-metadata normalizations in this replay.

The cache contains 139 Foundation modules and 872 compiled artifacts,
including the recorded companions. All 2,118 unique provenance/source/
artifact/toolchain/package/bundle pins matched before and after each fresh
invocation. Inherited source/trace authentication is retained in the pinned
input records. This is scoped reuse of those accepted objects, not a new
Foundation, package, or whole 455-module compiler replay.

Private output directory:
`/tmp/ha-consistency-normalization-independent-zqsk9jr1/lib`.
The two output paths were absent before invocation and are new regular
files, not symlinks. Cached dependencies alone are symlinked into the
private overlay. The original full source paths were passed to Lean; no
accepted source or shared object was overwritten.

Both commands use the pinned Lean 4.32.0 binary and
`-M6000 -j1 -DElab.async=false`, with `LEAN_NUM_THREADS=1`, explicit pinned
package search paths, no `LEAN_SRC_PATH`, and a checked 512MiB disk reserve.
The full commands and `/usr/bin/time -v` records are retained. Main passed
in 2.130 seconds; checks passed in 2.487 seconds. Maximum reported RSS was
2,254,080KiB and 2,241,612KiB respectively. Main emitted no diagnostics;
neither invocation emitted a warning or error. No failed peer metadata,
source, or compiler attempt occurred.

All eight axiom audits are retained. `sentence_empty_env` uses only
`propext` and `Quot.sound`; the seven fixed-source/proof results also inherit
`Classical.choice` in the Lean metatheory. These are standard Lean axioms,
not additional HA derivation constructors. No `sorryAx`, custom axiom,
native-decision oracle, or classical HA inference rule appears.

Independent object hashes, each equal to its author counterpart:

* Main: `69f6eb621b3ecaa9ae50c145af9c9020880c7c388cd043246b3a371c7bc1c8bc`.
* Checks: `4cf0de689be23fddcbc361df80a2cc3a6dfd856c44b68e38cca09c23f32e15c9`.

The durable independent summary is
[foundation-ha-consistency-normalization-peer-replay.json](foundation-ha-consistency-normalization-peer-replay.json),
SHA256 `7f34393a2315a3965b32f278ef38af79ff8b100ff73f762493247b3fcb79043b`.
Its sixteen-member source/input/driver/log/timing/result bundle manifest is
[FILES.json](foundation-ha-consistency-normalization-peer-replay/FILES.json),
SHA256 `3f7b2fa58adec39a599abc0d095c94b94b9710cb9f69dc21839638885e8da3e3`.
The object files are pinned in that evidence and retained in the private
output directory; they are not copied into the repository.
