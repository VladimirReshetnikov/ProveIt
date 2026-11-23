# Knot theory in intuitionistic primitive recursive arithmetic

Open **knot_theory_ipra.pdf** for the report. Its LaTeX source is **knot_theory_ipra.tex** together with the sibling chapter files. The linked table of contents and the final source map connect individual results to the requested topics.

## Reading paths

- For the first Tait conjecture, read the diagram conventions in §1 and the state, forest, and adequacy arguments in §6. The proof treats arbitrary competing diagrams, including the possible issue of a disconnected shadow.
- For constructive geometry, §§2–3 give rational regular projections, a faithful lifting lemma, unknotting in four-space, ribbon-to-slice conversion, and the descending-diagram shelling. §10 builds a rational triangulated Seifert surface.
- For computations, §§5, 6, 8 and 9 work through torus knots and links, the trefoil, figure-eight, Hopf link, Borromean rings and connected sums. §7 derives finite-type invariants from the integral expansion of the Jones polynomial.
- The formalization ledger is in §12. It distinguishes ordinary Lean theorems, proofs of object-language derivability and unfinished ProveIt integration.

## Rebuild the report

From this directory, with a normal TeX Live installation, run:

    pdflatex -interaction=nonstopmode -halt-on-error knot_theory_ipra.tex
    pdflatex -interaction=nonstopmode -halt-on-error knot_theory_ipra.tex

A third pass may be used if LaTeX requests one. The figures are drawn in the source using TikZ. There are no external fonts, images or data downloads.

## Run the checked artifacts

Use Python 3.10 or newer. The Alexander matrix checker uses SymPy (tested with 1.14.0). The other seven suites use the standard library.

    python -m pip install -r requirements.txt
    python run_checks.py
    python run_checks.py --lean

The last command also runs the four standalone modules with Lean 4.32.0. Set LEAN_BIN to select an explicit Lean executable. A successful run is recorded in verification.txt. No suite searches the network.

| File in code/ | What running it verifies |
| --- | --- |
| check_colorings.py | 266 Fox braid-count comparisons, 1,452 rational closure comparisons, and all 961 affine colorings of T(3,5) at the chosen parameters |
| jones_states.py | Open boundary pairings under II and III; curls, two-braids through eleven crossings, the figure-eight polynomial; grading and value at one on 341 short three-braids |
| alexander_braids.py | Symbolic Laurent braid matrices and first-minor gcds including integer content; negative and positive two-braids, mirrors, braid relations and stabilizations |
| check_borromean.py | All three component deletions, exact color counts for fourteen moduli, and the Jones span and four-slot specialization |
| descending_certificate.py | Warping-degree inequalities for 5,167 signed visit words; 126 spatial move and subdivision steps checked using rational geometry |
| polygon_caps.py | Rational polygon triangulation; boundary, area and dual tree on 42 examples |
| polygon_geometry.py | Rational regular-projection examples; moment-curve apex tests and eight cone-fan certificates |
| check_finite_type.py | Signed Jones differences for three braid families of examples at orders zero to two, including the nonzero second difference of the trefoil |

For example, run "python code/jones_states.py 3 1 -2 1 -2" to compute the normalized bracket of the figure-eight using a braid word. "python code/alexander_braids.py 3 1 -2 1 -2" computes its Alexander data. Both use positive generators for downward left-over-right crossings.

## Lean status and ProveIt integration

EquationalFox.lean defines an additive equational fragment, derives addition commutativity and associativity from its recursion equations by equation induction, and proves the three integral Fox identities on signed pairs in this syntax. The report gives a rule-by-rule interpretation of this fragment in ordinary iPRA. Fox.lean, SurfaceCore.lean and DiagramCore.lean are host-level Lean proofs or executable definitions. The four files were elaborated with Lean 4.32.0 using Std. None contains proof placeholders.

LocalIPRA.lean is a separate unbuilt candidate for the actual ProveIt sequent type. The repository's built library dependencies were unavailable here. To check it in a compatible built ProveIt checkout, run from that repository root:

    lake build IPRADerivations
    lake env lean /absolute/path/to/this/archive/lean/LocalIPRA.lean

The target revision is 6d03f3643ebb91a6243eb1e35e7599b388197786 of VladimirReshetnikov/ProveIt. The geometric and general invariant chapters include finite induction invariants and directions for extending the formalization. The general Reidemeister theorem identifying tame ambient isotopy with the diagram quotient is an external bridge. The arguments and the geometric witnesses specify separately what follows in the finite move calculi.
