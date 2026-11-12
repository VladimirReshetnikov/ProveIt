BOOLEAN-TESTED CONSTANCY FOR iPRA AND SMALLER PROOF CHECKERS
Prepared November 12, 2026

Start with ipra_boolean_constancy.pdf. The matching .tex file is standalone.

The package has two independent contributions:
1. A restricted constancy rule applied only to Boolean equality tests,
   with a selector-accumulator proof of full quantifier-free induction,
   and an explicit whole-domain identity bi-interpretation with iPRA.
2. Four complete implementations of the EXISTING scalar kernel.
   A final incoming-archive check found that the streaming 244-token and
   267-node profiles were already present. Their import spelling is four
   bytes shorter here. Only the compact byte frontier improves, 479 to 478;
   the fully validated native byte control improves 637 to 636. Their
   measured improvements do not measure the new constancy presentation.

Measured complete programs under CPython 3.12.14:
                     tokens   AST nodes  normalized bytes
checker244.py          244      272          604
checker267.py          249      267          602
checker478.py          274      304          478
checker636.py          346      392          636

The first two use JSON Lines and the appropriate three-field protocol.
The third retains a JSON stack and the guarded public-goal interface.
The fourth retains a JSON stack, checks exact integer/list input, and
validates the native Eq/D public grammar and scope.

The compact minima 244/267/478 belong to THREE DIFFERENT PROGRAMS.
The framing changes are explicit; the byte changes preserve canonical
public theorem sets while rejecting some old noncanonical certificates.
No single program dominates the current 244/267/479 envelope. No absolute
minimum or new checker-size record for the constancy theory is claimed.

Reproduce from this directory:
  python3 checkers/verify.py
  python3 mathematics/verify_boolean_absorber.py
  pdflatex -interaction=nonstopmode -halt-on-error ipra_boolean_constancy.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_boolean_constancy.tex

The first script checks source provenance, measures the programs, and
runs the ordinary/-O checker fixtures. It writes evidence under checkers/.
The second is a small symbolic sanity check, not a formal theorem prover.

The report and the supplied written proof arguments distinguish established
mathematics, imported results, finite tests, and remaining questions.
Independent review notes are under review/.

The original article source under reference/upstream_article/ is pinned to
b9aa36102e523213ae956b474ec651bfde3e5665 in VladimirReshetnikov/ProveIt.
It can be built separately with LuaLaTeX (three passes). Its references are
not the source of the new report's measurements. Upstream material uses
MIT No Attribution; see LICENSE-ProveIt.txt. New code and documentation in
this research package are likewise made available under MIT No Attribution.
