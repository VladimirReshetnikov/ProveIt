STRICT CHECKER REPRODUCTION

From any working directory, run:

    python3 /path/to/package/tests/verify_strict.py

This regenerates the named proof certificates and rejection controls, emits
matching X certificates for the three controls, runs all four standalone
programs in normal and optimized Python, compares the new traversal with the
original implementation, and remeasures whole modules. Outputs are:

    tests/strict_certificates/{rw,tr}/
    tests/strict_certificates/manifest.json
    evidence/strict_validation.json
    evidence/strict_metrics.json
    evidence/strict_metrics_table.tex
    evidence/gzip/*.py.gz

The recorded run uses CPython 3.12.14 and zlib 1.3.2. There are 38 fixtures:
14 valid derivations and 24 expected rejections. Four programs and two Python
modes give 304 process checks. The independent traversal audit contributes
1,200 comparisons. All matched in the recorded run.

For one closed theorem:

    python3 code/global_rewrite.py < tests/strict_certificates/rw/closed_large_marker_congruence.json

The checker accepts only by exiting normally and printing exactly ACCEPT
followed by one newline. Exceptions and resource failures are rejection.
The kernel uses no Python assertions, so python -O removes no proof checks.

The public certificate is an exact four-key JSON object:
    variables: nonnegative exact integer
    context: array of well-scoped formulas
    goal: well-scoped formula
    proof: a primitive proof tree

All syntax is the explicit tagged de Bruijn representation documented by the
report. Formula constructors are equality, Q and D. Numerical constructors
are variables, zero, successor and the scalar iterator. The full native
formula language is admitted. Every certificate component that supplies a
term or formula is validated or obtained from a checked inference; there is
no separate canonical-goal assumption and no hidden proof database.

generate_strict_certificates.py is an untrusted named proof producer. It builds
large-marker congruence proofs using only I0 and root rewriting, and also
supplies an independent logical fresh-name construction using DI, DE and QE.
Its translation option turns each named RW step into an X step by explicitly
abstracting the matched occurrences. The R and X fixture sets have identical
variable counts, retained contexts and claimed conclusions.

The original X comparator is OUR SEVEN-RULE ADAPTATION of the incoming
one_context package's direct checker: it replaces that checker's separate
introductions by the already-published witness-sensitive W introduction.
The other X files change only the traversal implementation. These are
supplied matched controls, not claims that an unchanged upstream file had
the same reported measurement.

The written universal equivalence proof is separate from these finite
implementation checks. Neither this Python checker nor the new R calculus
is presented as a newly verified Lean/Rocq development.
