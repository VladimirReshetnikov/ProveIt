DETERMINISTIC WITNESSES: COMPLETE CHECKERS AND FINITE VERIFICATION

checker_eight.py is the original eight-rule scalar native calculus with one
change: DI by cases has no witness field. Its witness is always the newest
ambient free variable, or zero if there are no ambient free variables.

checker_seven.py combines the same deterministic witness with the existing
diagonal-guard seven-rule calculus. Its mode is progressive exactly when the
raw matrix has the form I(y,y;h)=I(y,y;k), and is case mode otherwise.

The controls use exactly the same raw syntax, substitution, scope checks,
equality rule, proof format, and input/output boundary, except that their DI
node has an additional arbitrary witness term and validates that term.

Run all finite verification, exact pinned-code translations, and measurements:
    python3 verify.py

Run a checker:
    python3 checker_seven.py < verified/seven_naming_two.json

Success means exit code zero and exactly ACCEPT followed by a newline.
Exceptions and all other outcomes are rejection. Optimized Python is covered.

Every checker is a complete standalone file importing only json. No checker
imports verify.py, a producer, a translator, another checker, or a theorem
file. The files have no docstrings; all published source metrics count the
entire module after ast.unparse plus one final newline.

Exact CPython 3.12.14 metrics (tokens / AST nodes / normalized bytes):
    control_eight.py       979 / 1086 / 2834
    checker_eight.py       971 / 1078 / 2817
    control_seven.py       932 / 1029 / 2770
    checker_seven.py       924 / 1021 / 2753
The comparison is matched. The repository's compressed 516-byte checker is
shorter and has a different interface. No global size record is claimed.

The verified naming_two certificates derive H(2), where
  C(v,a,b)=I(v,a;u.b)
  H(y)=D_(x,v)(C(v,0,C(y,0,Sx))=C(v,0,y)).
Under the established ordinary reading this implies exists x, Sx=2.
No DI instruction supplies either 1 or any other chosen witness term.
The proof uses H(0), H(Sz), closure introduction and specialization at 2.

These finite checks establish no universal completeness theorem by themselves.
The parent research report supplies the mathematical proof. Restoring each
forced witness translates a checked proof into the corresponding old numeric
control. A separately implemented translator converts every positive fixture
into exact pinned tagged repository checkers; those checkers validate the
translated proof independently.

Repository comparison: VladimirReshetnikov/ProveIt
Pinned head: 9f9545f5ffd9e0392d4a36639503aca12383450a
Reference folder: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/diagonal_guard/code
The three files under reference/ are unchanged upstream copies. The helper
translate.py is used only by the untrusted fixture translator. The MIT-0
license is included in reference/.
