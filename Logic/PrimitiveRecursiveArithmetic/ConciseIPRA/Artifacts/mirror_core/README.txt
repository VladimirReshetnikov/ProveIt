A SMALLER INDUCTION SELECTOR FOR iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

START HERE
  ipra_mirror_core.pdf   Complete 28-page report, including inherited
                        arithmetic appendices and the entire selected checker.
  ipra_mirror_core.tex   Standalone LaTeX source, with all text and code embedded.
  code/mirror_six.py     Selected complete certificate checker.

RESULT
Keep the unrestricted raw numerical and formula languages of the current
ConciseIPRA native calculus. Keep Hyp, Refl, the two-case Eval, QE, and DE.
The single D-introduction chooses progress exactly at an uninstantiated
matrix of the literal shape

    a(x,y) = I(y,a(x,y);u.h(x,y,u)),

and chooses cases otherwise. This replaces SPrf's two-iterator diagonal
selector by a one-iterator selector. No public grammar restriction,
normalizer, term-template argument, or new arithmetic axiom is added.

The paper proves exact equality of all contextual raw sequents with the
native kernel, and direct admissibility of numerical substitution.
Composing this equivalence with the inherited native/iPRA bridge gives
both interpretation composites and equiconsistency with full first-order
iPRA. Both numerical domains are whole, equality is actual equality,
and both numerical composite isomorphisms have graph x=y.

SIMPLICITY AND ATTRIBUTION
The improvement is modest and measured against a matched complete
implementation of the current six-rule SPrf calculus:

  Program             Bytes  Significant tokens  AST nodes
  Diagonal control     3125           1022             1091
  Mirror proposal      3109           1012             1082

The only executable-source change is the DI guard. Both Eval cases count
as one rule family in both systems: six families, seven constructors.
This is not a repository-wide size record or an absolute minimality
theorem. The smaller compressed 516/788/820-byte interfaces are not beaten
by this tagged implementation.

The mirror shape is inherited from mirror_guard; Eval is inherited from
the current core; the preservation-with-provable-base substitution repair
is explicitly inherited from reflexive_base. The proposed contribution is
this particular unrestricted raw-language combination and its smaller
matched selector, with a complete equivalence argument. It is not a new
general substitution principle or an additional rule-count deletion.

VERIFICATION
The new metatheorems are written mathematical proofs. There is no new
Lean/Rocq verification of this calculus or of the Python checker.
Existing Lean source endpoints were read but not rebuilt; the included
Lean files are reference sources with external imports.

Executed evidence includes 23 direct fixtures (46 API and 92 normal/-O
CLI checks), 18 independent native replays (36 normal/-O CLI runs), and
72 numerical-substitution replays. It also includes a case introduction
whose base is consumed and a genuine substitution that changes the
selector from cases to progress. Both deliberately unrepaired controls
are rejected. All expected outcomes passed.

Counts overlap across execution interfaces; they are not counts of
independent mathematical phenomena. The exact ledgers are in evidence/.

REPRODUCE
Python 3.10+ is sufficient; the recorded measurement runtime is 3.12.14.
From the extracted directory, run:

  python3 reproduce.py

The checkers use only the standard library. Input/output and all certificate
fields are specified in code/FORMAT.txt. A checker's acceptance is exit
status zero and exactly ACCEPT followed by a newline. Any exception or
resource failure is rejection. Mathematical completeness assumes
unbounded resources, as in the baseline.

To rebuild the standalone source and PDF (requires pdflatex and the
standard TeX Live packages listed in the preamble):

  python3 build_report.py

Or compile the already assembled source directly with pdflatex twice.

CONTENTS
  paper_main.tex, ordinary_bridge.tex   Editable report components.
  build_report.py                      Assemble and compile the final paper.
  code/                                Complete checkers, transformations,
                                       certificate format.
  tests/                               Fixture generation, replay, metrics.
  examples/                            45 JSON certificates, including
                                       accepted and rejected controls.
  evidence/                            Measurements, normalized source,
                                       executable diff, verification, PDF QA.
  reference/                           Pinned mathematical sources and
                                       independently supplied old checkers.
  SOURCE_PROVENANCE.json                Authenticated source file identities.
  CLAIMS.json                          Scope and limits of claims.
  SHA256SUMS                           Delivered-file checksums.

The generic executable transformations cover mirror-to-native compilation,
derived case introduction, and numerical/hypothesis substitution. A generic
native-to-mirror induction compiler is not included; its construction is
proved in the paper. No empirical test replaces either interpretation proof.

PINNED BASELINE
  https://github.com/VladimirReshetnikov/ProveIt
  e1d9e3b12edd642ea2f5b572bb43febceaa50d93
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Reference material retains the supplied MIT No Attribution license in
reference/LICENSE-ProveIt.txt. New code may be used on the same terms.

The paper ends with further research questions. No repository file,
branch, commit, issue, or pull request was modified by this work.
