Suspended-unit experiment: reproducible negative size result
===========================================================

This directory contains the complete standalone checker for the report's
secondary UNIT presentation, its matched Step control, and 83 frozen positive
certificates. It has no dependencies outside this directory and uses only the
Python standard library.

The experiment adds a suspended update constructor U(a;u.h). The canonical
constructor contracts I(0,a;u.h) to a and factors I(Sc,a;u.h) into
U(K(c,a;u.h);u.h). It does not substitute into or evaluate the update body during
normalization. The primitive evaluation rule is:

    a=b, U(a;u.h)=r  ==>  r=h[b/u]

The other four schemes and their clause protocol are retained. Public terms
and formulas must already be canonical. The source validates all children
before contraction. This is a structural alternative explored during the
research, not the primary SeedEval proposal and not a checker-size improvement.

Reproduce from this directory:

    python3 measure_verify.py

The script validates the 83 frozen UNIT certificates in process and writes
metrics_verification.json. It measures every line of both acceptance modules
after removing the leading docstring and applying ast.unparse plus one final
newline. Significant tokens exclude whitespace, comments, and tokenizer
markers; AST nodes count ast.walk. Source SHA-256 values include docstrings.

Recorded with CPython 3.12.14:

                         Bytes   Tokens   AST nodes
    suspended_unit.py     2902      803         864
    control_step.py       2804      758         815

The suspended-unit version is larger in all three coordinates. The matched
control is the same shared-traversal Step implementation as code/control_step.py
in the main package; it is included here so the comparison is self-contained.
The frozen fixtures are the 83 upstream Step certificates with every supplied
term/formula replaced by its suspended-unit normal form, retaining the same
forward proof constructors. They are checked by suspended_unit.py, not by the
Step control. The Step control's tests are in the main code package.

suspended_unit.py is the measured exploratory source with only its leading
docstring corrected to describe suspended-unit normalization accurately.
Removing that docstring gives the same measured program. The tests are finite
implementation checks, not a proof of the structural equivalence in the note.
No additional negative tests or command-line process tests are claimed here.
