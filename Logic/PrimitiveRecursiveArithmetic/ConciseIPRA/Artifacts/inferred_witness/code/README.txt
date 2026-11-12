AUTOMATIC CLAUSE SPECIALIZATION: EXECUTABLE PACKAGE

This directory contains the complete Python implementation for the new
opening-synthesis presentation, its matched controls, actual proof
certificates, and reproducible validation. The mathematical report is the
authority for the bi-interpretation theorem; finite testing supplements
that argument and does not replace it.

Primary files
  checker.py                 complete unbounded checker
  checker_fuel.py            complete checker with explicit finite fuel
  FORMAT.txt                 syntax, all instructions, scope and CLI contract
  proof_tools.py             untrusted explicit certificate constructors
  build_examples.py          regenerate the 12 closed positive examples
  verify.py                  reproduce all local validation and measurements
  metrics.json               measured complete-source size coordinates
  verification.json          validation results and exact fuel costs
  guard_creation.json        open-sequent guard-change/repair regression

Comparisons
  control.py                 explicit-equality opening control
  control_fuel.py            its finite-fuel counterpart
  output_checker.py          synthesized substitution on exported conclusion
  output_control.py          explicit equality on exported conclusion

The equality-opening control uses the same representation and traversal
code, the same forward proof interface, the same context-count scope
convention and the same external document contract. Its elimination checks
an equality proof instead of synthesizing a name. It is deliberately named
a matched control, not misrepresented as a previously delivered program.

Reproduce from this directory
  python3 build_examples.py
  python3 verify.py
  python3 checker.py < examples/transport_at_zero.json
  python3 checker_fuel.py < fuel_examples/transport_at_zero.json

Validation at delivery
  CPython 3.12.14
  12 positive closed certificates
  38 malformed or unsound certificates rejected
  114 CLI checks, with ordinary Python and python -O
  12 primary-to-control translations with identical goals
  24 exact-fuel and one-less-than-needed checks
  a failed-to-successful guard substitution with explicit branch repair

The certificates exercise zero and nonzero transport sources, target zero,
nontrivial transport under a false-equation assumption, nested iterator
binders, nested D-formulas, ordinary elimination fallback, a synthesized
term containing its own fresh parameter, and use of the specialized clause
inside the branch. Additional independent validation is supplied separately
by the audit workstream; it is not included in these local test counts.

Measurements of the final sources
                      bytes  tokens  AST  gzip9
  checker.py           1990     683  771    819
  control.py           1998     676  765    812
  checker_fuel.py       2203     728  826    885
  control_fuel.py       2211     721  820    880
  output_checker.py    1990     683  771    819
  output_control.py    1983     663  751    812

The measurements use ast.unparse plus one trailing newline, significant
tokenize tokens excluding encoding/endmarker/newline/NL/indent/dedent/
comment tokens, and ast.walk nodes. gzip9 uses compresslevel=9 and mtime=0
on normalized bytes and is an informational coordinate. A leading module
docstring is excluded, matching the historical package's method. None of
the selected files depends on an external macro library for acceptance.

The selected automatic opening is eight normalized bytes shorter than
the matched explicit-equality opening control. It has seven more tokens
and six more AST nodes. Therefore the rule-premise deletion is NOT claimed
as a uniform reduction in all implementation coordinates. The separately
reported reduction from the delivered 2273-byte witness-discharge checker
also includes forward inference and shared implementation simplifications.

The 516-byte compact codec and 788-byte validated-public-goal implementation
in the repository remain smaller source records under their own contracts.
The present package makes no claim to beat those records or to establish
an absolute minimal axiomatization. The normalization layer is real trusted
code, is fully included, and is not treated as free notation.
