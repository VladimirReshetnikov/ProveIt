A REGISTER-GRAPH PRESENTATION OF INTUITIONISTIC PRA
Research report on the ConciseIPRA proposal, November 10, 2026

READ FIRST

ipra_register_graph.pdf is the paper. Its complete LaTeX source is
ipra_register_graph.tex. The primary theory is counter-aware register
iteration, with numerical terms consisting only of variables, zero,
and J(n; old_counter, old_register. body).

The mathematical improvement is a smaller numerical grammar and a much
shorter arithmetic bootstrap: successor and the independent initializer
are derived, predecessor and selection require no induction, and all
ordinary primitive recursion compiles in one extra iteration without
pairing. The paper proves whole-domain bi-interpretability with full
first-order iPRA, including both internal interpretation composites.

This is NOT an established new minimum for complete proof-checker size.
The graph axiom is richer and J binds two variables. The readable complete
checker for the new theory is larger than the old compact checkers.
The separate 288-AST checker implements the OLD scalar calculus; its
measurements must not be attributed to the new J theory.

CONTENTS

  ipra_register_graph.tex / .pdf
      Self-contained paper, explicit logical and arithmetic rules,
      full main equivalence proof, scalar variant, comparison and limits.

  code/checker.py
      Complete standalone natural-deduction checker for the new theory.
      Includes syntax, scope, simultaneous capture-avoiding substitution,
      alpha equivalence, arithmetic schemas, equation induction, JSON
      parser and public closed-theorem interface.

  code/README.txt
      Exact certificate syntax and rule fields for that checker.

  code/test_checker.py and code/certificates/
      Untrusted certificate producer and regression harness; 24 positive
      and 28 negative fixtures, run normally and under Python -O.

  code/register_iterator.py
      Scalar one-body-variable semantic illustration; 644 assertions.

  code/counter_register_iterator.py
      Counter-aware semantic illustration, including the direct R compiler;
      385 assertions.

  code/pr_to_register_ast.py
      Actual finite-description compiler into only variable/zero/J ASTs,
      with independent source and target evaluators and capture tests.
      To keep expanded syntax smaller it uses the equivalent instruction
      S(C(Z(i), h(P(i), r), a)), whose endpoint values agree with the
      paper's S(C(i, a, h(P(i), r))).

  ancillary/checker_288.py
      New AST profile of the inherited native scalar calculus:
      604 normalized bytes, 261 tokens, 288 AST nodes, gzip-9 355 bytes.
      This is a one-node AST improvement over the inspected 289-node
      profile, not a byte improvement or new J checker.

  ancillary/reproduce_288.py and ancillary/reference/
      Exact parent and 36 upstream fixtures, plus false-major controls.
      150 public-driver executions were checked. See the included
      PROVENANCE_AND_SIMULATION.txt for the written simulation and the
      inherited malformed-input/resource qualification.

  reference/
      Pinned current README, old byte and AST leaders, and upstream license.

  evidence/
      Measured source sizes, detailed test receipts and review notes.

REPRODUCE

Use CPython 3.12.14 to reproduce the reported normalized-source metrics.
The programs otherwise use only the Python standard library.

  python3 reproduce.py

The checker accepts a closed-theorem certificate on standard input:

  python3 code/checker.py < code/certificates/functional_coverage.json

The other fixture filenames are listed in code/certificates/. Acceptance means exit
status zero and exactly ACCEPT followed by a newline. Any other outcome
is rejection. Tests and semantic evaluators are not trusted imports of
either standalone checker.

To compile the paper with an ordinary LaTeX installation:

  pdflatex -interaction=nonstopmode -halt-on-error ipra_register_graph.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_register_graph.tex

Repeat the second command if LaTeX requests another cross-reference pass.

The source uses standard LaTeX packages. No external figures, bibliography
processor, shell escape, internet access, or generated TeX include file
is required.

EVIDENCE LIMITS

The metatheorems are written mathematics reviewed during this research
run, not Lean/Rocq proofs. Finite tests do not establish universal
soundness or bi-interpretability. No literature-wide novelty or absolute
minimality claim is made. Exact comparison snapshot:

  VladimirReshetnikov/ProveIt
  8662bc0a00f4e77e482f7d141d7a4f919f70f9aa
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The adapted equality-reflection argument and reused checker sources are
attributed in the paper and provenance notes. The repository's MIT-0
license is included. No repository changes were published.
