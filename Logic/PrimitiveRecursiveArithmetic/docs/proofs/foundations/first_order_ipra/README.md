# First-order logic in intuitionistic primitive recursive arithmetic

Read **first_order_ipra.pdf** for the full argument. The main LaTeX source is **first_order_ipra.tex**. Its included chapters are in the same directory. The source guide at the end of the manuscript connects individual results to the starting article and ProveIt.

## Results and scope

The report contains 46 numbered theorems, propositions, lemmas and corollaries. It gives uniform numerical constructions for proof recognition and transformation, finite Tarski and Kripke soundness, monadic and Bernays–Schönfinkel decision, ground resolution and cut-free Herbrand extraction, finite Ehrenfeucht–Fraïssé games and separating formulas, graph nondefinability, computation encodings, and compactness obstructions. It also gives a fixed-formula completeness scheme using syntactic worlds.

The ambient theory is first-order intuitionistic arithmetic with primitive-recursive symbols and quantifier-free induction. Classical deductions and finite two-valued interpretations are objects of that theory. The numeric statements, fixed-formula schemes, and ordinary external model-theoretic readings are identified individually in the manuscript.

## Build the manuscript

Run these commands beside this README with a standard LaTeX installation containing amsmath, amsthm, mathtools, lmodern, microtype, geometry, booktabs, tabularx, enumitem, fancyhdr, xurl, hyperref and bookmark. Repeat if your first build requests another pass for cross-references.

    pdflatex -halt-on-error first_order_ipra.tex
    pdflatex -halt-on-error first_order_ipra.tex
    pdflatex -halt-on-error first_order_ipra.tex

## Replay the checked material

The included Lean files use only Std and the compiler pinned in lean-toolchain. They have no dependency on a ProveIt checkout. With Lean 4.32.0 on PATH and Python 3.10 or newer, run

    python verify.py

For the Python examples alone, run

    python verify.py --python-only

A particular compiler can be selected with --lean /path/to/lean. The verify script checks the files and prints the kernel axiom dependencies of the selected endpoints. The transcript of the delivered version is **verification.txt**.

| File | What is checked |
| --- | --- |
| lean/NegativeTranslation.lean | Full first-order translations of typed derivations both ways, including equality and quantifiers, finite Tarski soundness, and consistency of the pure calculi |
| lean/Substitution.lean | Finite Boolean semantic substitution, renaming, coincidence and identity substitution for scoped syntax |
| lean/BackAndForth.lean | Rank invariance from a winning back-and-forth position |
| lean/CanonicalForcing.lean | Truth lemma and canonical completeness of the propositional negative fragment with possibly inconsistent worlds |
| lean/GroundResolution.lean | A resolution checker and proofs of soundness and constructive refutational completeness |
| ef_certificates.py | Finite relational EF games, construction and evaluation of separating formulas, order threshold examples |
| code/normal_certificates.py | Checked resolution trees and equality-sensitive Bernays–Schönfinkel examples on clausal input |
| code/machine_witnesses.py | Rejecting finite Horn interpretations and extraction of accepting runs from finite time/stack data |
| code/finite_invariants.py | Monadic rank profiles compared with EF games, and the relational-to-directed-graph encoding on finite examples |
| native/equality_transport.json | A concrete open equality sequent in ProveIt's native scalar calculus |

For the native certificate, **native/README.md** identifies the external checker by revision and SHA-256 and gives its one-command replay after download. With that file saved locally, the positive replay and both negative controls can also be run with

    python verify.py --native-checker /path/to/raw_checker.py

The Lean proofs are metatheorems of the displayed calculi. The manuscript gives the proof and development plan for the other results, including how to construct the uniform numerical theorems inside ProveIt's ordinary Prf PRAAx judgment. The archive contains one separately checked native open sequent. SHA256SUMS covers all other archive members.
