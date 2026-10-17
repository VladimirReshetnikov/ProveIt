# Internal proof renaming and named generalization

`ModelCodedProofRenaming` proves named generalization for the actual internal
ZF and ZFC proof predicates in every IΣ1 model:

```text
Provable ZF  p  → Provable ZF  (namedAll chosen p)
Provable ZFC p  → Provable ZFC (namedAll chosen p).
```

Here the proof, formula and chosen variable may all be arbitrary internal
codes. The final statements have no standard-code, freshness, closed-matrix,
shift-fixed-matrix or undischarged axiom-closure premise. In particular, the
literal decoder truth formula's free label zero is allowed. These are
existence-of-internal-proof results; this package does not construct a
represented function selecting the output proof code.

## Proof construction

`ModelCodedRenamingSets` first constructs the finite image of any raw sequent
under the checked syntax-renaming operation. Actual IΣ1 HFS Σ1 replacement
proves a unique image. The fixed Σ1 graph is chosen before the arithmetic
model, and totality gives Δ1 definability. Images are total on raw inputs;
formula-set preservation and SHIFT compatibility retain their typing premises.
Empty, insertion, subset and single-term substitution laws are checked.

For fixed internal `chosen,total`, the proof-code induction predicate is

```text
Derivation T d →
  ∀ level ≤ total, ∀ offset ≤ total, d+level+offset ≤ total →
    Derivable T (setRename chosen level offset (fstIdx d)).
```

This is Σ1: source derivation is Δ1, target derivability is Σ1, sequent-image
computation is total Δ1, and both counter quantifiers are bounded. The proof
uses actual IΣ1 order induction. There is no output-proof bound or Π2
induction premise.

All ten internal derivation constructors are handled. Every child proof code
is strictly smaller than its parent, paying for ALL's `level+1` and zero-level
SHIFT's `offset+1` within the same fixed budget. Positive-level SHIFT reduces
`level` and applies the target SHIFT rule. The existential rule preserves a
typed renamed witness term and uses exact substitution compatibility. The
other cases use literal constructor, negation, image and inclusion laws.
The generic helper states its exact syntactic axiom-closure resource. Actual
ZF/ZFC corollaries discharge it with the already checked literal Δ1 axiom
recognizers, including the schema cases.

At the root take `total=d, level=offset=0`. The checked identity

```text
free(bindOneAt(chosen,0,p)) = rename(chosen,0,0,p)
```

then permits the actual target ALL rule and yields named generalization.
This argument transports arbitrary internal derivations, rather than only
quotations of externally finite derivations.

## Checks and provenance

Pinned Lean 4.32.0 checked both new modules and their focused audits, with one
thread and a 4 GiB limit. Sets passed on its first proof attempt; Proof passed
on its second. Sets reports 10 named axiom probes and 10 callers; Proof reports
7 probes and 8 callers. Both have zero warnings and use only `propext`,
`Classical.choice` and `Quot.sound`. Source/audit times were 3.177/1.981 s and
6.032/2.031 s respectively.

The Sets guard verifies exactly 11 project predecessors; the Proof guard
verifies exactly 14, reusing the passed Sets object. Both verify six external
source/object boundaries, the actual compiler and Omega provider, pinned clean
Foundation/Mathlib source checkouts and the dependency manifest, with actual
first-provider and input checks before and after. This records selected cached
object identities; it is not an independent attestation of the entire external
cache. No dependency was built or fetched.

The initial failed Proof attempt needed only arithmetic-addition placement,
explicit `0+1=1` normalization and unused-binder cleanup. The theorem contracts
and ten main cases were unchanged. The history record embeds every local
prepare/build record, all ten Lean snapshots and the exact executed guards.
Its historical recheck explicitly identifies the two changed live paths in
the initial Proof preparation and confirms the other 52 inputs unchanged;
the original guard and source bytes remain recoverable. No claim is made that
those two old live paths still have their initial hashes.

Four portable preflights passed, including copied project-object cache
relocation, plus five rejection controls. They perform no proof builds;
compiler validation does invoke `lean --version`. The Foundation namespace and
external objects remain explicitly reused in that relocation test.

## Reproduction

From the repository root, with the pinned dependencies and recorded caches
already available:

```sh
python Logic/Interpretability/ZFCinPA/check_model_coded_renaming_sets.py --output /absolute/fresh/sets
python Logic/Interpretability/ZFCinPA/check_model_coded_proof_renaming.py --output /absolute/fresh/proof
```

Both accept `--repo`, `--dependency-root`, `--source`, `--audit`, `--lean`,
repeated ordered `--library-path`, and `--prepare-only`. The first accepts
`--syntax-evidence`, `--syntax-cache` and `--syntax-audit`; the second accepts
`--renaming-evidence`, `--sets-evidence`, `--project-cache`, `--sets-source` and
parent-audit overrides. Both accept `--namespace-cache`, whose `Foundation/`
subdirectory must supply the existing complete namespace mirror. Cache
relocation must preserve every selected object hash; the scripts never build
missing predecessors. Remove `--prepare-only` only when holding the serialized
compiler slot.

## Remaining translation boundary

This package supplies all-internal named GEN for actual ZF/ZFC, including
formulas with free parameters. It does not yet translate all twelve C254 proof
rows into target proof codes, or prove the PA-internal C254/ZFC consistency
comparison. Checked decoder and propositional/constructor adapters are separate
prerequisites. Their remaining row templates and schema calibration must be
connected by an eligible internal proof induction; external completeness alone
does not provide that comparison.
