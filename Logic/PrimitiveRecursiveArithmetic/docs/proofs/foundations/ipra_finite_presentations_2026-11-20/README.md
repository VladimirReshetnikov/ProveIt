# Finite presentations and cyclic proof replay in iPRA

Open **main.pdf** for the full argument. The source starts at **main.tex**. Each TeX input file in the same directory belongs to the report, including the source for the frame/nerve figure.

## Results and verification level

- The general rule-table construction computes least closed sets, rank certificates and all inclusion-minimal sufficient supplies. The analysis of input-length path replay identifies its exact relation to the permitted induction schema.
- `lean/CyclicReplay.lean` checks stage inclusion for the executable procedure, stabilization, the minimal-support characterization, and the proof generator `ScopedReplay.replay`. For a fixed rule table and local proof providers, this theorem concludes an actual `Prf PRAAx` judgement. `two_supports` gives the object-language disjunction for a cyclic example. The internal theorem with a variable-size table and a reflected label predicate is proved on paper.
- The applications give exact polyhedral chart margins, a finite sheaf reflector, an inverse-tower stabilization criterion and coherent group lifts, a chain nerve theorem over F₂, homotopies with explicit moduli for closed rational boxes, and a local basis for the integer-resonant Gauss equation. The other five Lean files check the mathematical lemmas identified in section 7. Full object-level formalizations of the application chapters remain open.

## Reproduce the checks

The numerical checks use only Python's standard library. Use Python 3.10 or later.

    python3 verify.py

The five files `AtlasCase`, `CategoryCase`, `SheafCase`, `TopologyCase`, and `Resonance` require only `Std` from Lean 4.32.0. They can be run individually, for example with `lean lean/TopologyCase.lean`. The sixth module imports ProveIt's ordinary calculus and Mathlib's finite-set cardinality lemmas.

Use the [ProveIt source snapshot](https://github.com/VladimirReshetnikov/ProveIt/tree/3ee850b4c2d650cf01263823fd5415963747c5d0). In a checkout of this revision, prepare the standard pinned dependencies and run:

    lake build +ConciseIPRA.PR +Mathlib.Data.Finset.Card

Then run the following from the extracted archive, substituting the actual checkout path:

    python3 verify.py --proveit /path/to/ProveIt

A configured Lean environment with the same imports on `LEAN_PATH` can run `python3 verify.py --lean` directly. The local verification used that mode. The transcript in `verification/results.txt` records all six exact computations and the typechecking and axiom reports. Absolute filename prefixes in the transcript are normalized to the archive root.

To rebuild `main.pdf`, run the following in the archive directory with a standard TeX Live installation including Latin Modern, AMS packages, TikZ, microtype, and hyperref:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

## Verification inputs

| Component | Pinned identifier |
| --- | --- |
| ProveIt tree revision | 3ee850b4c2d650cf01263823fd5415963747c5d0 |
| Mathlib revision | 81a5d257c8e410db227a6665ed08f64fea08e997 |
| Lean release | 4.32.0, compiler commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35 |
| `ConciseIPRA/Syntax.lean` Git blob | a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348 |
| `ConciseIPRA/Deduction.lean` Git blob | 0969040f77fdd3ed9526e360e7a998584b4d9d8c |
| `ConciseIPRA/PR.lean` Git blob | 3251631592070d9ed3687cc0bf7dbd5eb452e46f |

The three ProveIt modules were freshly compiled from these blobs using the pinned Mathlib provider. `verification/SHA256SUMS` records every other distributed file.
