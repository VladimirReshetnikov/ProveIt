# Fresh helical and exact-construction refinements

Pinned repository: `1e2a853935a6155cbcf2aa199aaca51946c4fff9`.
All source paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.
These changes are narrowly new residual applications, not claims to invent
periodicity or canonical witness reuse as general techniques.

## 1. Recognize period-one rigidity instead of repeating integer induction

Targets: `WangTiles942HelicalQuotient.row_zero_of_helix` (file line 22) and
`WangTiles942SeamColumns.seam_iff_zero` (line 42).

The helix law says `T(x+w,t-1)=T(x,t)`. For fixed x,t, set

    f(s) = T(x+w*s,t-s).

The given law proves `f(s+1)=f(s)` in one step. Thus `f` has integer period
one. Mathlib's `Function.Periodic.int_mul_eq` gives `f(t)=f(0)` for every
integer t, positive or negative. Simplifying the endpoints gives precisely
`T(x,t)=T(x+w*t,0)`. No positivity of w, rectangular period, finite type, or
additional tile hypothesis is introduced.

The candidate proof uses only one local periodicity witness and the library
theorem. The original proof's successor and predecessor branches, associated
algebraic calculations, and induction generalization disappear. This is not
the already proposed centered interval induction: it identifies an actual
period-one function and delegates the whole integer orbit argument to an
existing API.

For seam columns, the already proved `seam_successor_iff` supplies period one
for the proposition-valued function `SeamAt T x`. Propositional extensionality
converts its iff to equality; `int_mul_eq` then makes the status constant at
all signed times. The theorem's statement and absence of a global periodic
plane assumption remain unchanged.

Two complete module overlays and `patches/helical-rigidity.patch` are supplied.
Full-file physical line counts are 147 -> 136 and 106 -> 102: 15 fewer lines,
with no helper module, import, or executable definition added. These are scoped
measurements on the pinned current files, not a globally merged hypothetical
tree of all earlier reports.

`HelicalRigidity.lean` checks both generic proof kernels against Lean 4.32.0.
Its successful log reports `[propext, Quot.sound]` and no `sorryAx` for both
theorems. The complete current production modules and their four original focused
Checks modules subsequently compiled successfully. Five existing endpoint
axiom reports are byte-identical before and after; the new exact-witness
helper uses only `propext`, `Classical.choice`, and `Quot.sound`.

The mathlib API is in `Mathlib/Algebra/Ring/Periodic.lean` at package revision
`81a5d257c8e410db227a6665ed08f64fea08e997`; its standard integer-multiple theorem
already contains the two-sided group argument.

## 2. Expose the exact band quotient before existential packaging

Targets: `WangTiles942CycleBand.marked_word_of_halt` (line 136) and
`WangTiles942BandMarker.canonicalWord_properties` (line 79).

Both current proofs independently invoke `extension_properties`, normalize
the same left/right seam coordinates, invoke the helical quotient matching
theorem, and restrict the quotient binding back to the canonical band.
The first hides the constructed quotient in an existential. The second needs
the literal `canonicalWord`, so it reconstructs the whole proof despite using
the same expression.

The new lower-level `band_quotient_properties` proves matching and pointwise
binding of that exact quotient once. Its result starts with a `let a :=`
containing the existing `quotientWord (extend (band ...)) ...` expression.
There is no new data structure, new quotient, or changed canonicalWord.

The original existential theorem becomes a packaging wrapper around this
exact result. The later canonical theorem takes the same matching/binding
pair and adjoins `canonicalWord_marker_iff`. Its `canonicalWord` definition
and every existing public theorem statement remain byte-identical.

The hierarchy matters: the shared theorem resides in CycleBand, before
marker uniqueness. It cannot import marker facts or assume the desired
uniqueness conclusion. The original width, height, and actual-halting
hypotheses remain visible, and both nonzero instances are supplied exactly
as before by the existential wrapper.

The net total is deliberately modest: CycleBand 167 -> 179 lines, BandMarker
124 -> 108, for four lines saved after charging the full new theorem statement
and documentation. The useful simplification is that the substantial
extension/quotient proof has one maintenance site. There is no claim of a
large source-size improvement or faster compilation.

`patches/exact-band-witness.patch` and the two complete overlays are supplied.
No source artifact is pushed. Integrators should rebase these local proof
changes onto their current tree rather than replace full modules that may
already contain other proposed improvements.

## Novelty boundary

The incoming ZIP audit is in `incoming-exclusions.md`. The independent a-r
auditor checked all report/notes files and Lean prototypes for the named
helical/cycle-band targets and mechanisms. No corresponding proposal was
found. Closest precedents were the earlier generic cyclic residue interfaces,
coherent source/window witnesses, and same-original-word selector coherence.
Those principles are assumed available; the new work is the exact residual
period-one argument and duplicated new completeness-construction elimination.

Round o already warned against adding a general additive quotient framework
for short periodic-plane wrappers. These proposals keep the existing
coordinate representation and do not add such a framework.


## Completed validation

* Freshly compiled 34 pinned repository modules including the four original
  focused `Checks` modules. Mathlib/package cached artifacts were used only
  after checking their Git revisions against the pinned lake manifest.
* Four complete candidate production modules and four original focused checks
  pass. Nine modules were recompiled after source/dependency hash invalidation;
  the remaining matching prerequisites come from that fresh local baseline.
* Five existing endpoint axiom reports are byte-identical before/after. The new
  `band_quotient_properties` uses the same three standard axioms as its clients.
  No `sorryAx` appears in an audited endpoint.
* Both integration patches pass `git apply --check` together.
* Four changed theorem headers and the complete `canonicalWord` definition
  were compared directly and are identical.
* Source total across the four modules: 544 -> 525 physical lines (19 saved).
  Final hashes and metrics are in `metrics-final.json`.

Evidence files in this directory include `FINAL_RESULTS.json`,
`validation.json`, `axiom-comparison.json`, `signature-audit.json`, baseline
and candidate audit logs, and the focused-build logs. Baseline and candidate
source/dependency/output hash records are in the sibling `wang-base` and
`wang-candidate` output directories; compiled object files should not be
included in the user-facing archive. This is not a full repository build or
a controlled compilation-performance benchmark.
