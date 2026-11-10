ARBITRARY POSSIBLE OUTPUTS IN MODELS OF PA
========================================

Requested by Vladimir Reshetnikov. Prepared November 9, 2026.

Main result
-----------
There is one partial computable program e which diverges on every standard
input, but for every standard natural number n there is a first-order model
of PA satisfying the arithmetical sentence "e(0) halts with output n".
The witness includes a program code and a fixed arithmetization of its
computation. The program is not a total function in the standard model.

The paper gives a complete mathematical proof. The Lean files give a
concrete formal target, a proof of the abstract logical core, and an assembly
theorem applying Mathlib's existing Kleene recursion theorem. Arithmetic
representation and effective proof-search obligations remain to be filled
for the concrete PA instance. This is a proof outline with source files,
not a claim of a completed end-to-end Lean formalization.

Contents
--------
pa_flexible_output.tex       LaTeX source of the paper.
pa_flexible_output.pdf       Compiled paper.
lean/Statement.lean         Concrete Foundation syntax, computation formula,
                           model-existence target, and named obligations.
lean/ProofCore.lean         Logic-only proof relative to explicit interfaces.
lean/MathlibAssembly.lean   Conditional assembly using fixed_point₂ directly.
notes/api_audit.txt         Existing API names, pins, and important pitfalls.
notes/mathematical_audit.txt Independent mathematical review notes.
dependencies.json          Exact repository/dependency revisions and URLs.
verification_status.txt    Precise verification and completion status.
lean-toolchain             Lean version of the inspected ProveIt snapshot.
scripts/build_pdf.sh        Rebuild the PDF with three pdfLaTeX passes.
scripts/check_lean.sh       Check the three Lean sources sequentially in a
                           prepared ProveIt environment.
SHA256SUMS                 Checksums of the packaged deliverables.

Rebuild the PDF
---------------
Run:
  bash scripts/build_pdf.sh

Lean checking
-------------
No Lean or Lake executable was available in the authoring environment.
The Lean sources were reviewed against pinned upstream source, but were
NOT compiler-checked. The mathematical proof and its remaining formal
obligations are documented separately.

Use an existing ProveIt checkout at the revision in dependencies.json,
with its Foundation submodule initialized and imported modules compiled.
Then run:
  bash scripts/check_lean.sh /absolute/path/to/ProveIt

The script invokes one Lean process at a time and does not automatically
build the full repository. Respect ProveIt's instruction to compile missing
dependencies one module at a time; do not launch simultaneous Lean builds.

The definitions in Statement.lean are actual propositions and formulas.
They are not declarations asserting that those propositions are true.
In particular, FullySpecifiedMainClaim is the appropriate final endpoint:
it includes correctness and functionality of the chosen arithmetization.

Connection to the supplied reference
------------------------------------
Hamkins's exposition of Woodin's universal algorithm gives a stronger
result. Waiting for the first enumerated value gives the requested partial
function. The paper also proves the single-output result directly by a
self-referential search for refutations. It explains why the shorter route
requires less new Lean infrastructure than the end-extension theorem.

No repository changes, commits, or pull requests were made.
