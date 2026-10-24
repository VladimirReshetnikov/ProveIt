# Retained logical calibration interfaces

These files are exact, unmodified copies of sources retained in the incoming
`ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24` archive.
Their Git blob hashes also match the corresponding files in the ProveIt snapshot
used for this work:

- Repository: <https://github.com/VladimirReshetnikov/ProveIt>
- Snapshot: `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`
- Inspection date: 2026-10-24

## Repository paths and byte identity

| Retained file | Actual repository path | Git blob SHA-1 |
| --- | --- | --- |
| `KEndpoint.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` | `bdf3a570fe02e5e0becf6c12f562957cf03fc8d5` |
| `ConstructibleChoice.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` | `0f14fc8890363d7abb9c4e9aa89cae80553735cc` |
| `KCode222.lean` | `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean` | `9d10efed97ce2aacc8592bd37023b91deea709fe` |

The hashes above are Git blob hashes, including Git's blob header, rather than
plain SHA-1 hashes of the file contents. They were compared with `git ls-tree`
at the pinned snapshot, and the copied bytes were checked for exact equality.

`KEndpoint.lean` and `ConstructibleChoice.lean` were copied from the archive's
`provenance/norm_legacy/inherited/root_fusion_provenance/upstream_ordinary/`
directory. `KCode222.lean` was already retained under
`intake/ConZFC_Shell_Reciprocal_660_2026-10-24/ConZFC_Shell_Reciprocal_660/upstream/ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/`.
No retained `KSeedDirect222.lean` was found in this incoming archive, so that file
has not been added here. The repository path cited by its import is
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedDirect222.lean`.

## Exact interface statements

`KEndpoint.lean` contains the proof-bearing declaration

```lean
theorem c222_iff_zf_refutation :
    KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  ⟨KUpper222.zf_refutation_of_c222, c222_of_zf_refutation⟩
```

This declaration appears before the later section with machine, tape, coverage,
and boot hypotheses. The calculus-to-ZF interface itself has no such
hypotheses. The reverse direction, `c222_of_zf_refutation`, has a proof body
using the calculus completeness theorem, the named-formula seed property,
and `zf_consistent_of_formSeed`. Its mathematical argument turns a hypothetical
non-derivability model into a ZF model, which a finite ZF refutation excludes.
The forward direction invokes `KUpper222.zf_refutation_of_c222`.

`ConstructibleChoice.lean` contains the proof-bearing declaration

```lean
theorem zf_refutation_iff_zfc_refutation :
    BProv ZFax_s [] Form.fBot ↔ BProv ZFCax_s [] Form.fBot :=
  ⟨BProv_theory_mono (fun _ hb => Or.inl hb), choice_refutation_remove⟩
```

It occurs after `section Model` has ended; the model parameters in that section
are not assumptions of the displayed refutation equivalence. One direction is
inclusion of the ZF axioms into ZFC. The proof of `choice_refutation_remove`
uses first-order soundness and completeness together with the constructible
class model of ZFC inside a model of ZF. This is the inherited ordinary
mathematical ZF/ZFC equiconsistency argument.

`KCode222.lean` is included as the retained definition of the finite calculus
and its code constructors. It helps identify the object referenced by the
first interface; it is not an additional independently rebuilt certification.

## Verification scope

The immediate bodies and surrounding declaration scopes of the two interface
files were inspected. Both displayed interfaces are unconditional theorem
declarations with proof terms, not declared axioms, `sorry` placeholders, or
conditional assumptions. No `axiom`, `sorry`, or `admit` declaration occurs in
either immediate interface file.

This package did **not** freshly rebuild the complete Lean import graph or
re-audit every transitive dependency for axioms or placeholders. The retained
files therefore document established upstream calibration dependencies of the
ordinary mathematical proof. They are not a new end-to-end kernel certificate,
and no claim is made that the entire transitive import graph was independently
verified here. Nor is a new object-level ZFC derivation supplied by these copies.
The report states the ordinary mathematical equivalence and explains its
internalization in ZFC, with the calibration identified as inherited work.

The calculus equivalence has no K215 execution hypothesis. Some imports and
other theorems in `KEndpoint.lean` concern machines, so a stronger claim that
its entire import graph contains no machine-related material would be false.
