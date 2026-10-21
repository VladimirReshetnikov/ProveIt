# Bounded single-use lemma census

Source-only next-checkpoint proposal. The current phase9 sources, all proof
objects, public endpoints and producers remain untouched. No compiler or
maintained proof producer was invoked.

The census pins the eleven adopted phase9 modules plus `DomRho8`, `KSeed222`,
`KSeedModel222` and `DominatedImplication`. It finds 374 top-level declarations,
including 250 theorems, in those fifteen files. Of 106 private theorems, 64 have
one direct application and 67 have one caller declaration. These are different
notions: a single caller can invoke a lemma several times. Neither count is a
reason by itself to inline a proof.

`census.py` strips nested comments and strings and indexes identifier tokens
across 32,362 current BusyBeaver Lean source files. It is a conservative source
census, not Lean elaboration: public basenames can collide, notation/implicit
elaboration is not resolved, and the count does not establish an external API
contract. Selected removals are private simple identifiers whose complete local
reference sets were also manually read. `census-summary.json.gz` keeps all
counts and all private/one-caller reference locations; bulky common-name lists
are omitted. The full raw occurrence ledger remains in scratch, with its hash
recorded. The first repeated-regex census was stopped for exceeding the intended
survey time and replaced by a one-pass token index; its source/status is retained.

## Two small candidates

| File | Proposed change | Before → after | Saving |
|---|---|---:|---:|
| KHomeReady | Inline private `rowsCheck_sound` into the first conjunct of `ready_sound` | 4,657 → 4,572 bytes; 101 → 100 lines | 85 bytes / 1 line |
| DominatedImplication | Inline `b12` into `b13`, `b15` into `b16`; put `b60`'s body directly in the retained named `basisK` | 19,378 → 19,128 bytes; 381 → 373 lines | 250 bytes / 8 lines |

Total: 335 bytes and nine lines, removing four private declaration boundaries.
These are modest readability improvements, not a substantial endpoint-size or
kernel-time result. Both candidates are **uncompiled**. The exact drafts and
unified diffs are included; `candidate-control.json` checks every retained
public header, every executable definition and every untouched proof body.
Imports and all axiom-report commands also remain identical.

The rows checker is short mechanical unpacking of the two finite row lists;
putting it at its sole use removes a navigation step. The deeper
`boundary_of_check` and `overlay_eq` remain separate because they identify the
actual arbitrary-frame argument. The core's two truth eliminations are each
one modus-ponens application with a simple variable substitution; they add no
large schema instantiation to their consumers. Removing the numbered `b60`
wrapper retains the useful mathematical name `basisK` and its original type.
All other implication proof nodes remain opaque shared steps.

## Names deliberately retained

- `KZipTape.run_normal`, `trim_eq_of_getD`, `rel_unique`, and the step/run/window
  bridge lemmas isolate invariants; inlining their inductions would make the
  endpoint proofs harder to inspect. `trim_eq_of_getD` is used twice by its one
  caller, so naive inlining would also duplicate its proof.
- `KHome.zeros`, `ones`, `scanBound_tail`, `stripBlank_shape`, `home_word`, and
  `home_sound` separate word algebra, conservative scan bounds, marker handling
  and the semantic shortcut. Their one-caller status does not make them redundant.
- `KDecoderPrefix215.entry_run` is used twice by `entry_uniform`; keeping it
  prevents duplication of full-frame transport. The route/leaf/walk endpoints,
  including currently unused public ones, are part of the intended adapter API.
- `KSeed222` and `KSeedModel222` need no edit. `diagonal_bundle_of_seed` isolates
  the essential a=b case; `clos_iff`/`bundle_iff_seed` expose semantic boundaries;
  the one-line `seed_of_bundle` preserves the named, audited reverse interface.
  The tiny `matrix_marker` normalization is clearer as a named fact about the
  private binder. A parallel full read by the reflection agent reached the same
  recommendation; no new compiler or formal peer receipt is claimed here.
- DomRho8 is now a compatibility adapter. Its public `rho8_all_of_restricted`,
  `composition`, `lift_right`, and legacy numerical helpers remain unchanged.
- Generated one-use `b*`/`cd*` nodes with large substitutions stay named. Flattening
  all 64 single-use private proofs would replace a readable checked hierarchy
  by deep proof terms and could change elaboration cost. No such blanket rewrite
  is proposed.

`KRuntimeCore.incr_ne_nil` has no direct named caller in this scope; this is a
possible separate dead-export review, not an inlining change. It is retained.

## Producer obligation before any adoption

`DominatedImplication.lean` is generated. The proposed source is not ready for
adoption until `generate_dominated_implication_lean.py` and its pinned suffix
template reproduce it. `producer-plan.md` names the exact minimal changes and
metrics controls required. The historical input certificate and its validated
shortcuts must stay unchanged. No current generator or template was edited.

The next authorized check should compile each isolated candidate and compare
axiom reports, then regenerate the core from the synchronized producer. Any
provider invalidation must include transitive source/import dependencies, as
required by the corrected phase9 build policy. There is no reason to rebuild
the whole site corpus just to decide whether these small candidates elaborate.
