AN EXPLICIT DIOPHANTINE SPECIALIZATION FOR Con(ZFC)
22 October 2026

Read report.pdf; report.tex is its editable source.
Pinned ProveIt revision: cdd582bec13f908df3711fa9e05d1ddac368a5db

PRIMARY CONSTRUCTION
native/k215_native82_source.json is one polynomial in 18 strictly positive
integer unknowns, exact degree 187, with an 82-operation shared-expression
schedule (46 multiplications and 36 additions/subtractions).
All six coefficients are fixed by native/k215_native_definition.py and the
bundled, hash-pinned k215.tm. No unknown machine index or existential coefficient
is left. The full window alphabet and the enormous coefficient numerals are NOT
materialized. The coefficient recipe is an explicit finite mathematical
definition, not a claim that its full evaluation is feasible in CPython.

The theorem is absence of positive integer solutions iff Con(ZFC), by the
mathematical reductions formalizable in ZFC set out in the report. This is NOT
an unconditional consistency proof. It is NOT a newly kernel-checked Lean/Rocq
endpoint or an encoded internal ZFC derivation. The existing native universality
proof chain is imported by reference; finite tests do not replace it.

ALTERNATIVES
- native/nine_equation_system.txt and k215_native72_system.json: nine equations,
  20 positive unknowns,72 comparison operations; their single SOS polynomial
  has98 operations and exact degree 84.
- native/quadratic_system.json:82 quadratic equations in 180 nonnegative
  unknowns. Their sum of squares is a quartic polynomial.
- tag/tag_alternative.txt: explicit finite coefficients and 11 equations in 22
  nonnegative unknowns, with SOS degree at most 348. Its general arithmetic
  compiler theorems are already in Lean; the new fixed adapter and composite
  endpoint are not newly compiled. A complete 131144-slot counter program is
  included, together with its reproducible generator.

DOMAIN AND SIZE WARNINGS
Positive means 1,2,...; natural means 0,1,...; all subtraction is over integers.
To turn18 positive inputs into natural inputs substitute each v=x+1.
To use arbitrary integers, substitute v=1+a^2+b^2+c^2+d^2:72 unknowns, degree 374.
Never simply allow signed inputs in the native polynomial.
Fixed coefficients and their bit sizes are uncharged in the82/72/98 counts.
No global minimum, practical coefficient expansion, or new universal bound is
claimed. The fixed-input specialization saves two operations, not a universal
ordinary-input algorithm improvement.

REPRODUCE BOUNDED CHECKS
Use Python 3.10 or later with its standard library, without -O unless explicitly
shown below. These are own finite checks; predecessor JSON receipts are inert.
From the extracted archive root:

  python3 native/k215_native_definition.py
  python3 native/audit_native_specialization.py
  python3 -O native/audit_native_specialization.py
  python3 native/audit_polynomial.py
  python3 native/audit_nine_equations.py
  python3 tag/audit_k215_tm0_adapter.py
  python3 tag/compile_k215_counter.py
  python3 tag/tag91_closed_formula_toy_audit.py

The two tag compiler commands regenerate their bundled tables/receipts in place;
the delivered results were checked byte-for-byte against fresh packaged runs.
None of these commands invokes k215_coefficients or expands the giant constants.
Do not invoke that full enumeration merely to run the regression tests.

The exact source-fold audit covers 82/72/98 schedules, all gates/ports live,
256 algebraic evaluations and four compiler-layout fixtures. The independent
factored-form check covers 120 integer/rational assignments. Arbitrary diagnostic
coefficients in these checks are not claimed admissible program coefficients.
Machine finite-prefix checks do not decide eventual halting.

To regenerate the quadratic AST, run native/make_quadratic_lift.py.
To build the report, run pdflatex report.tex twice with the standard geometry,
amsmath,amssymb,amsthm,enumitem,hyperref,fancyhdr,longtable packages.

PROVENANCE
SOURCE_PINS.json lists inspected original source/data bytes and pinned links.
SHA256SUMS.json binds all distributed files except itself.
LICENSE.ProveIt is retained for reused repository data. See NOTICE.txt for scope
and attribution. No original predecessor Python code or compiled proof objects
are needed or included for the bounded checks.
