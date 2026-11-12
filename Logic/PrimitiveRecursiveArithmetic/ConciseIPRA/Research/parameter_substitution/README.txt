PARAMETER SUBSTITUTION IS ENOUGH FOR iPRA
Research note on the ConciseIPRA proposal, November 12, 2026

RESULT

Proper-subterm equality replacement can be restricted to FREE NUMERICAL
PARAMETERS. A nonvariable source is used only for equality joining at the
root or for reversal of the minor equation. A fresh-alias construction
recovers arbitrary term-template transport.

The theory keeps raw iterator terms and ordinary capture-avoiding
substitution. Its public formulas are equality and D_(x,y) B, read as
exists x (B(x,0) -> forall y B(x,y)). Contexts contain reusable clauses.
Its five instruction families are Compute, Param, Use, Open, and Close.
Compute contains TWO explicit computation axiom schemas. Reflexivity,
general equality transport, cases, and equation induction are derived.

The paper proves exact consequence equivalence with the native calculus,
both formula round trips, and therefore whole-domain bi-interpretability
and equiconsistency with full first-order iPRA through the inherited
native/iPRA bridge. Equality is actual equality; both numerical composite
isomorphisms have graph x=y.

START HERE

ipra_parameter_substitution.pdf   Complete 16-page mathematical report.
ipra_parameter_substitution.tex   Standalone editable LaTeX source.
code/raw_parameter.py             Complete standalone proof checker.
FORMAT.md                        Exact syntax and certificate contract.
code/translate_raw.py             Checked proof compilers in both directions.
code/verify_raw.py                Reproducible finite validation suite.
examples/                        Small selected accepted/rejected examples.
code/raw_examples/               Complete supplied control/target examples.
evidence/                        Results, measurements, audit, provenance.
reference/bridge/                Unchanged inherited arithmetic proofs.
reference/                       Exact source evidence and comparison code.
paper/                           Editable report fragments.
build_report.py                  Reassemble the standalone LaTeX file.
reproduce.py                     Run checks and regenerate normalized sources.
measure_comparisons.py            Verify seven bundled incoming comparisons.

MEASURED COMPLETE PROGRAMS

CPython 3.12.14; module docstring removed; ast.unparse plus one line feed.
All parsing, syntax validation, scopes, opening, rules, and CLI are counted.

Program                              Bytes   Tokens   AST
Pruned matched template control       2907      765    881
NEW RAW PARAMETER CHECKER             2857      769    892
Shared-opener template control        2937      777    895
Filed raw three-case Eval             3046      853    993

The strongest matched comparison saves 50 bytes (1.72%) while adding four
tokens and eleven AST nodes. This is a mathematical restriction and a
local byte improvement, NOT a simultaneous improvement in every metric.
The new checker is not the smallest complete program in the repository.
Compact protocols remain much smaller. A refinement of the existing
two-case Eval calculus considered during this work is also smaller:
2731 bytes / 741 tokens / 862 AST, supplied as a comparison source.
No absolute minimum or arithmetic-foundation breakthrough is claimed.

REPRODUCE

    python3 reproduce.py
    python3 measure_comparisons.py
    python3 code/raw_parameter.py < examples/reflexivity.json
    python3 code/raw_parameter.py < examples/used_induction.json
    python3 code/raw_parameter.py < examples/reject_direct_zero_rewrite.json

The first two example certificates print ACCEPT and exit zero. The third
must print REJECT and exit nonzero. The checker does not use Python
assertions for acceptance and is tested under ordinary and optimized Python.

The public JSON object has exactly goal and proof. The goal is closed.
The usual JSON parser last-key behavior applies to duplicate textual keys.
See FORMAT.md for the integer/list term language and all five instructions.

    python3 reproduce.py --pdf

also rebuilds the PDF using pdfLaTeX. The delivered main .tex file is
standalone and can be compiled directly. The Python code needs only the
standard library. Physical Python resource limits still apply to very
large valid certificates.

VALIDATION

38 accepted closed examples; 26 adversarial rejections; 76 checked
forward/backward translations; 2402 syntactic opening checks; 800 independent
semantic opening checks (zero skipped); 12 parameter-boundary checks;
128 public CLI runs, including Python -O. All expected outcomes hold.

Finite tests support implementation claims. The mathematical equivalence
is a written proof. No new Lean or Rocq formalization is claimed, and the
upstream Lean project was not rebuilt. Its already formalized bridge is
identified by exact source files and theorem names in the report.

PROVENANCE

Repository: VladimirReshetnikov/ProveIt
Revision: 5d85023b0688e03b75f0ec3a04bb43ef0bb51705
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The 56 indexed research packages and five incoming archive descriptions
were reviewed, with relevant full sources fetched for the comparison.
Fresh aliases and the clause interface are inherited ingredients; the
new result isolates the strictly weaker equality interface they require.
No priority outside this scoped repository review is claimed.

Original material carries the included MIT No Attribution license. New
code, proof notes, and scripts may be reused under the same terms.

