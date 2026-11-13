A ZERO-TEST SPLIT FOR INTUITIONISTIC PRIMITIVE RECURSIVE ARITHMETIC
12 November 2026
Comparison snapshot: f577c326a0e97bd956392d7426092ed6499da327

START HERE
  ipra_zero_test_split.pdf
  ipra_zero_test_split.tex and sections/zero_test_split.tex

MATHEMATICAL RESULT
In the ordinary scalar theory, replace successor coverage
    n = 0 or exists m, n = S(m)
by
    n = 0 or I(n, S(0); u.0) = 0.
Keep the two iterator computations, separation 0=S(0) -> false,
intuitionistic first-order equality logic, and literal-equation induction.

The new case axiom is exactly equivalent to coverage. An equationally
derived predecessor P gives the decomposition
    n = C(Z(n), S(P(n)), 0),
where C(v,a,b)=I(v,a;u.b) and Z(n)=C(n,1,0).
The two ordinary theories have identical theorems, so the inherited
whole-domain iPRA bi-interpretation is unchanged.

The paper specifies all logical and nonlogical rules and proves the new
equivalence, a fixed-induction-instance formulation, and a product-model
obstruction to replacing the case principle by zero decidability.

CHECKER RESULT AND LIMIT
  checker/code/compact478.py
    271 significant tokens / 305 AST nodes / 478 normalized bytes
  checker/controls/compact479.py
    272 significant tokens / 304 AST nodes / 479 normalized bytes

This is one byte smaller. The independent token and AST records remain
248 and 270. The exhibited family envelope is (248,270,478), attained
by DIFFERENT programs. This is not a global minimality theorem.

The compact checker assumes the existing canonical CLOSED GUARDED Eq/D
public grammar and finite exact-integer/list certificate alphabet. It does
not validate those entire syntax conditions. Its last JSON item is now
[goal, initial_floor]. Use initial_floor 0. Convert an old certificate:
  python3 checker/compile_certificate.py < old.json > new.json
  python3 checker/code/compact478.py < new.json

For arbitrary JSON with full native public-goal and whole-input alphabet
validation, the unchanged 637-byte implementation is supplied:
  python3 checker/controls/strict637.py < old_format_certificate.json
Its last item is the old public goal, WITHOUT a scope header.
It is prior work, not a new size record.

DO NOT GENERALIZE THE HEADER EDIT TO THE UNRESTRICTED NATIVE INTERFACE.
The negative experiment contains a false native formula accepted by that
invalid mutation. It is not a guarded public goal. Rejected mutations are
generated only temporarily by reproduce.py and are not usable checkers.

REPRODUCE
  python3 reproduce.py

CPython 3.12.14 reproduces the exact normalized measurements. The suite runs
546 isolated compact-checker regressions, 12 negative-experiment checks,
and 1000 finite arithmetic examples. Those examples are not proofs of
the mathematical induction claims.

BUILD PAPER
A normal LaTeX installation with the packages listed in the source suffices:
  pdflatex -interaction=nonstopmode -halt-on-error ipra_zero_test_split.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_zero_test_split.tex

CONTENTS
  checker/        Standalone checker, readable expansion, compiler, frozen
                  controls, 66 inherited fixtures, and verification receipt.
  evidence/       Metrics, source census, independent review, counterexample,
                  and reproducibility receipts.
  reference/      Inherited written proof sources with provenance; optional
                  57-node predecessor; selected Lean sources for the
                  equational dependency boundary.
  sections/       New mathematical argument included by the main paper.
  CLAIMS.json     Machine-readable claims and exclusions.
  MANIFEST.sha256 File integrity manifest.

FORMAL STATUS
The new argument is a written mathematical proof. The inherited Lean
sources are reference material; no new Lean/Rocq compilation or end-to-end
formal verification of the Python checker is claimed. Test evidence and
mathematical proofs have different roles.

Inherited material is identified and retains the supplied ProveIt license.
No remote repository was modified.

