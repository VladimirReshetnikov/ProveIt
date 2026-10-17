# Closing ordinary parameters of open interpreted templates

`OpenTemplateClosure.lean` turns internal proofs of an ordinary source template
at every finite predicate buffer into a proof of that source formula's ordinary
universal closure. Predicate interpretations may be arbitrary typed internal
formulas and may retain arbitrary additional internal free parameters. Only
the ordinary source parameter range is generalized.

The generic `generalizeAll` theorem shifts all pre-existing internal free
parameters above an externally fixed fresh-coordinate range. It substitutes
`fvar i` for bound coordinate `i`, then applies the internal universal proof
rule in Foundation's exact closure order. Its vector identity handles both the
new zero coordinate and successor coordinates. The two-variable audit client
checks that this order is not exchanged.

For `closeTemplate`, the ordinary source `fixitr 0 fvSup` moves the source free
coordinates into bound positions. The resulting source formula has no source
free variables, so shifting its translation is exactly translation at the
shifted predicate family. The fixed fresh substitution restores the original
ordinary source formula by Foundation's `subst_comp_fixitr`. The exact
`0+fvSup` arity is retained where required by the source syntax API; it denotes
the same finite count and introduces no extra binder. The source formula,
free-variable range and closure count remain externally finite. This is not a
claim about a nonstandard internal source-proof length or closure count.

The hypothesis supplies a target internal proof at every external finite
buffer. This module does not itself supply schema callbacks, a Collection
proof, arbitrary internal source-proof transport or a numerical/binary
consistency endpoint. Those are separate obligations. In particular, absence
of source free variables is never used to assume that the interpreted internal
matrices are free-variable-free or shift-fixed.

The pinned Lean 4.32 focused check passed the final source in 2.691990s and the
audit in 1.827315s: four ordered axiom probes, four generic caller examples,
standard axioms only and zero warnings. It reused 16 matching project
source/object providers and seven external boundaries. All 58 inputs and the
fresh object were checked before/after. The whole Foundation cache was reused;
no dependency was downloaded or rebuilt and no whole-cache attestation is
claimed. The actual first Init and Omega objects were validated.

Five nonpassing attempts remain preserved. Four failed during source
elaboration: recursion/normalization, an unavailable empty-set lemma spelling,
and the exact finite-arity interface were repaired without increasing a
resource option. The universal-closure proof was split into explicit syntax
normalization lemmas. The fifth attempt passed the complete source but failed
the Type-valued caller audit because it lacked `noncomputable section`. Adding
that audit annotation produced run6, the first complete source/audit pass.
Every original record, executed driver, source/audit snapshot and exact repair
diff is archived separately. Partial source passes and preflights remain
explicit nonpasses or unbuilt records.

A portable focused replay uses the existing built dependency checkout and
matching predecessor evidence:

```sh
python3 Logic/Interpretability/ZFCinPA/check_open_template_closure.py \
  --repo /path/to/Proofs \
  --dependency-root /path/to/built/Proofs \
  --output /outside/new-empty-directory
```

The maintained predecessor evidence is selected by default. `--open-evidence`
can relocate its exact frozen record; project and Foundation namespace cache
options may relocate matching built objects. Every selected source/object and
the actual first providers must retain the recorded hashes. The portable
checker is byte-identical to the successful executed driver.

`--prepare-only` validates the providers and snapshots inputs without compiling
the source or audit; compiler-version discovery may run. The maintained-default
preflight passed as `PREPARED_NOT_BUILT`. Redundant rejection/relocation controls
were explicitly waived and are not claimed. The independent final review read
the complete source, audit and guard and bound run6 to its current inputs and
fresh object without replaying Lean.
