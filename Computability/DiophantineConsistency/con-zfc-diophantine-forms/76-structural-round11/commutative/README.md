# Height-bounded commutative proof certificates

This module replaces the round10 common-multiple certificate by a growing coefficient-height register. It eliminates the whole second bounded-universal block and the three per-step label-bound witnesses. The three local tradeoffs are20 witnesses/degree50,21/20, and23/14. The last preserves the previous local witness count while lowering degree50 to14. Five exposed coordinates are not included in these counts.

The new global mathematical source is proved equivalent to the same calibrated C222 refutation predicate. A closed ordinary-polynomial constructor is specified, but is **not compiled, materialized, or claimed as a smaller completed consistency equation**.

Files: `HEIGHT_CERTIFICATE.md`, `section.tex`, `height_shared_step.json`, `build_height_step.py`, `check_height_certificate.py`, and the generated Lean constructor. The inherited local Horn polynomial remains byte-exact from round10.

Rebuild order: build_height_step.py; emit_height_constructor.py; build_height_selector.py; build_height_boolean.py. Checks: check_height_certificate.py; check_height_selector.py; check_height_boolean.py. All are authored, and support normal and optimized Python.

The proof and report section also record an exact four-outer-parameter variant obtained by replacing M0 with the final height beta value. It adds a remainder graph inside the bounded step, so no compiled-size improvement is asserted; the generated constructors retain the five-parameter form.
