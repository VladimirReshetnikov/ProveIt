# Transport and finite observations in iPRA

Open **report.pdf** for the complete argument. The entry point for the LaTeX source is **report.tex**. Its section files, bibliography, figure and figure source are included.

The report gives effective path transport, finite local systems over a presented groupoid, inverse moduli for rational polyhedral maps, a detour around integer translates of hyperplanes, and a resonant Gauss basis and its monodromy. The theorem on the Gauss basis is uniform for Gaussian rational parameters with integer \(c-a-b\). The theorem matching the Gauss series at zero also assumes that \(c\) avoids the nonpositive integers.

## Reproduce the finite checks

Use Python 3.10 or newer. The five reference checks use its standard library.

~~~sh
python3 verify.py
~~~

The programs use exact rational or finite-table arithmetic. The period in the circuit diagnostic is displayed in decimal after its rational inequalities have been checked. The optional figure script uses NumPy and Matplotlib. The prebuilt vector figure is included.

## Reproduce the Lean checks

The ordinary iPRA judgment is ProveIt's `LeanProofs.ConciseIPRA.Prf PRAAx`. Five files construct embedded derivations. The five other files prove host-level lemmas. Section 9 states the endpoints and specifies the arithmetic needed for the full results. The continuum theorems are human proofs with formalization plans.

The research snapshot is `3ee850b4c2d650cf01263823fd5415963747c5d0` of [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/3ee850b4c2d650cf01263823fd5415963747c5d0/Logic/PrimitiveRecursiveArithmetic). Use its root project and its pinned Lean 4.32.0 toolchain. In a configured checkout at that revision, build the upstream targets:

~~~sh
lake exe cache get
lake build IPRADerivations.Core.Powers IPRADerivations.Core.SumOrder IPRADerivations.Core.Tactic
~~~

From this packet run:

~~~sh
python3 verify.py --proveit /absolute/path/to/ProveIt
~~~

The runner lists the provider revision, checks all five programs and ten Lean files, and prints Lean's axiom report for the selected endpoints. It requires `lake` on PATH. `verification.txt` records the successful run. Kernel checking used already-built dependencies at provider revision `09fe17194da14cdd100947737952e44100bb71b8`. The complete source trees of the imported ProveIt libraries had identical Git tree IDs at that revision and the research revision.

| Provider input | Identical Git object ID |
| --- | --- |
| `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA` | `1a0ba095608217955539e58d32522defb0f0549a` |
| `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core` | `0f87b1d29d2b12f91ebb7ffe00e5c98d4f8f190a` |
| `lean-toolchain` | `94b9f495baff80fd9cb44aad8f4762cb3b2066fe` |
| `lake-manifest.json` | `dc6d553da8d0ca6a9ad926545920d21f9dc6b4c7` |

ProveIt source modules imported by the check files are all in the two listed trees. The mathlib dependency is pinned by the manifest. Some derivations use upstream Lean metatheory with `propext`, `Quot.sound`, and `Classical.choice`. Their object-level conclusions are proofs in ordinary intuitionistic primitive recursive arithmetic. The reported axiom checks found no `sorryAx`.

## Rebuild the PDF

In a TeX Live installation with `latexmk`, run `bash build.sh` from this packet. All figure assets are included. Relevant mathematical comparisons and links to the specific repository sources are in the report bibliography.
