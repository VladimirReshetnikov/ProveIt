# Quotient detachment for the native ZFC code calculus

This directory is a self-contained Lean 4.32.0 proof artifact. It contains
106 upstream source modules from ProveIt commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959` and four new source modules.
Every upstream file is byte-for-byte bound to that commit's Git blob ID in
`pinned_source_audit.json`. No prebuilt project `.olean` files are included.

## Result

For the repository's actual `Code254` decoder, let `Valid(n)` mean truth
under every assignment in an irreflexive structure with two distinct
elements. Then

```
Valid(a) → Valid(h) → h / 4 = P(a,b) → Valid(b).
```

The quotient rule accepts all four constructor tags. Universal truth of a
membership atom is impossible; a universally true equality atom forces
its numerical variable indices to be equal; the quantifier case follows
by instantiation; the implication case is ordinary detachment. The
assumptions about two distinct elements and every assignment are essential,
as the checked counterexamples show.

The enlarged `Q222` calculus starts with `C222` theorems and closes under
this rule and theorem-only generalization. The final theorem is exactly

```lean
SetTheory.BusyBeaver.ZFC.QuotientEquivalence.q222_iff_zfc_refutation :
  Quotient222.Q222 Code254.F ↔ BProv ZFCax_s [] Form.fBot
```

This is an unconditional theorem about finite derivability. Its printed
axioms are `propext`, `Classical.choice`, and `Quot.sound`. No consistency
axiom, `sorryAx`, or theorem-set conservativity assumption is added.

## New modules

| File under `lean/` | Main contribution |
| --- | --- |
| `QuotientDetachment.lean` | The code-valued inference theorem and sharp counterexamples |
| `Quotient222.lean` | The enlarged calculus and its semantic soundness |
| `QuotientCalibration.lean` | The upper bound through the existing constructible-model theorem, using the empty set and its successor as distinct domain elements |
| `QuotientEquivalence.lean` | The inherited lower bound and the exact refutational equivalence with ZFC |

The lower-bound proof copies the short mathematical argument from
`KEndpoint.c222_of_zf_refutation`, followed by `Q222.base`. Its dependency
on `KLowerQHyp` avoids importing unrelated machine simulation endpoints.

## Rebuild

From the final archive root, with Lean 4.32.0 on `PATH`:

```sh
python3 quotient/verify_quotient.py --build-dir /tmp/proveit-quotient-check
```

Use `--lean /absolute/path/to/lean` to select the executable. The build
directory must be empty. The driver verifies the source hashes of the
complete import closure, copies only source files into that directory,
sets `LEAN_PATH` to it, and compiles all 110 modules in dependency order.
It writes `build_manifest.json` and a separate log for every module.

An optional `--repo /path/to/ProveIt` uses the corresponding checkout's
upstream sources instead of the bundled copies. It requires the same
recorded source hashes. A source-only check is available with `--check-only`.
Neither operation contacts GitHub.

`verification/` contains the final clean-build manifest and compiler logs.
The four new modules' logs include the explicit axiom reports.

## Scope

This artifact checks the mathematical enlarged-calculus equivalence. It
does not rebuild or claim a new binary-machine endpoint, a 215-state
realization, or a 214-state result. The accompanying report treats the
quotient source macro, compiler-transfer argument, finite regressions,
and physical state-allocation experiment separately.

All original code algebra, first-order logic, set-theoretic calibration,
and constructibility results are inherited from Vladimir Reshetnikov's
ProveIt repository. Their source contents are unchanged in this bundle.
