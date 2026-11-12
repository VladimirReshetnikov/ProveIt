# Independent implementation audit

**Result:** no soundness, scope, or rule-correspondence defect found in
`checker.py`. This is a written source review with focused finite tests,
not a proof-assistant verification.

Audited checker SHA-256:
`a803a62dd07adbb26276dcf464669b90f6a7c5157231e962fc71d581b43be2cd`.

## Scope and substitution

The scope convention is coherent: free parameters are numbered
`0,...,n-1`, and an eigenparameter is appended at `n`. Extending the
parameter scope therefore does not renumber old parameters. Numerical
binders use ordinary de Bruijn indices and shift those free parameters.

`map_term` adds one binder only for an iterator's body. `map_formula`
adds two for D and one for Q, and does not traverse Q's integer tags as
terms. `substitution` replaces the chosen slot by the suitably shifted
image and lowers larger indices. `witness_body` removes x at slot 1,
shifting the supplied witness to retain y at slot 0. These operations
match the stated binding conventions, including nested iterator bodies.

DI validates its witness in the old scope; its new parameter consequently
cannot occur in the witness. QI admits only a literal-equation matrix.
DE checks its original context, matrix parameters, and conclusion before
extending the scope, so its eigenparameter cannot escape. All rule
premises are recursively scope checked.

## Rules and replacement

All eight branches implement their stated native rules. I0 and IS check
the literal computation equations; IS uses capture-avoiding substitution
of the entire recursive iterator value. QE checks both its closure major
and its base instance. DI and QI correctly use S(n), and DE opens its
witness at n rather than reusing an existing parameter.

BRep checks the major equation, then computes precisely the minor
`Rep_target^source(destination) = result` from the goal
`result = destination`. `replace_term` tests a whole node before
descending, stops after a match, and shifts both comparison and inserted
terms under an iterator body. A source containing the target does not
cause cascading replacement. No supplied template or occurrence mask is
trusted. The optional restriction forbidding literal-zero sources is NOT
implemented; the checker implements the unrestricted theorem.

The marker generator in `test_checker.py` has the correct reversed major
orientations, namely `source = marker` and `target = marker`. Its marker
is larger than the template, and its contextual substitution preserves
passive occurrences of the original source. The five generated
congruence tests cover passive, repeated, unused, and nested occurrences.
I separately replayed the supplied complete certificates
`congruence_passive_copies` and `congruence_nested_iterator_binders`; both
were accepted.

## Strict input and driver contract

Term variables, scope counts, hypothesis indices, and Q tags exclude
Booleans through exact integer-type checks. Term/formula arities and all
proof-node field sets are checked. No user-supplied executable code,
arithmetic oracle, or unchecked theorem step is present. The public
driver requires both n=0 and an empty context; the open-sequent API does
not silently become an axiom mechanism for the closed-theorem driver.
The checker does not use Python assertions, so `python -O` does not
disable its validation.

## Focused additional tests

`independent_audit.py` adds four positive sequents and two invalid
certificates, with results in `independent_audit_results.json`:

- A free replacement target is kept distinct from an iterator's bound
  variable; a forged match is rejected.
- A nonconstant D opening with two existing outer parameters actually
  extracts and uses the freshly appended witness. Replacing that new
  witness by an old parameter is rejected.
- A complete closed certificate introduces a name for zero, opens it,
  extracts b=0 by QE and computation, uses that equality, and discharges b.
- A nonconstant progress step preserves an old arithmetic parameter
  while using the new parameter as its counter.

The closed naming certificate was accepted by the driver both normally
and under `-O`; the open naming sequent was rejected by that driver in
both modes. All six sequent checks and all four driver runs had their
expected outcomes. No implementation change was needed.

One coverage observation: the original fixture named
`bound_variable_must_not_match_free_source` uses numerical zero as its
replacement target and would reject for additional counter/seed
differences. The original direct operation test checks the intended
bound/free distinction correctly; the new certificate-level pair tests
it directly with a free-variable target. This is a test-specific
observation, not a checker defect.

The mathematical equivalence proof remains separate from these runs.
Finite tests and manual review do not establish a universal machine-checked
correctness theorem for the Python implementation. Physical recursion
and memory limits can reject very large valid finite certificates, as
already stated in the package documentation.
