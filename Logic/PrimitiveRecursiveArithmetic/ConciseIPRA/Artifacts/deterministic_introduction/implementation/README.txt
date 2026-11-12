SEPARATE IMPLEMENTATION REFINEMENT OF THE EXISTING NATIVE CALCULUS
================================================================

This directory does NOT implement the new mathematical calculus presented in
its enclosing report. It independently simplifies the already existing native
proof checker while retaining its public formulas and certificate format.

Selected result
---------------
code/native.py is a complete standalone checker. Its initial public-goal type
check and first variable-scope check share one traversal. The existing depth
parity already determines whether a node is a numerical term or a formula.
An internal local phase argument enables the additional public type checks
only during that first traversal. Every subsequent proof-kernel operation is
unchanged. The JSON input cannot set the phase argument.

CPython 3.12.14, ast.unparse normalization and one final LF:

Complete module                 Bytes   Tokens   AST nodes   gzip9
controls/native780.py             780     360       409        458
code/native.py                   656     333       379        388
controls/compact508.py            508     267       302        330
code/compact_optional.py          506     267       303        328

The selected native checker saves 124 normalized bytes (15.90%), 27 tokens
(7.50%), and 30 AST nodes (7.33%) against its exact current control. All parsing,
public-goal validation, substitution/scope checks, proof inference and output
code are included. No support script or control file is imported by either
selected checker. Gzip9 is informational only.

The optional compact program merely spells the integer decrement k-1 as
~(-k). It saves two bytes, ties tokens and adds one AST node. Its scope-floor
value is always an integer, so this identity leaves every computation and
accepted trace unchanged. It is a small encoding improvement, not a change
to the mathematics. The compact program has its existing canonical
integer/list and guarded-public-goal contract; unlike the native program,
it does not include a separate general public-goal grammar validator.
The two profiles should not be compared as though their input contracts were
identical. No single program improves all corpus-wide coordinate minima.

Verification
------------
Run:

    python3 reproduce.py

Only the Python standard library is needed. The executed suite compares
20,030 arbitrary JSON initial-goal shapes, 10,000 generated grammar/scope
shapes, 42 complete-certificate trace pairs (including unused-prefix counts),
and 84 paired CLI cases under ordinary and optimized Python (168 process
executions). It checks each profile against its own frozen control. The
native and guarded compact profiles intentionally classify some auxiliary
fixtures differently. All comparisons passed.

The 21 inherited fixtures include substantive computations, transport,
compound logical introductions/eliminations, induction with a used hypothesis,
and attacks on scope, future witnesses, false majors, and false conclusions.
The arbitrary-JSON scan also exercises booleans, floats, strings, null,
objects and malformed list arities at the public native interface.

PROOF.txt proves universal successful-trace equivalence. Finite executions
support the implementation but do not replace that proof. There is no new
Lean/Rocq verification. Practical Python memory and recursion limits apply;
the mathematical equivalence idealizes sufficient resources.

Examples
--------

    python3 code/native.py < fixtures/computation_zero_local.json
    python3 code/compact_optional.py < fixtures/computation_zero_local.json

Acceptance is exit status zero with exactly ACCEPT followed by a newline.
All other results reject. Both modules read a JSON proof stack from standard
input and consume it from the end, as in the controls. The final stack element
is the public goal. Unused prefixes are permitted and remain identical in
successful matched executions.

Files and provenance
--------------------
code/native.py                 Selected complete native checker.
code/compact_optional.py       Optional byte-only compact refinement.
controls/                      Exact existing complete source controls.
fixtures/                      Exact inherited finite regression certificates.
PROOF.txt                      Universal comparison proof for both refinements.
reproduce.py                   Portable untrusted audit and measurement script.
metrics.json                   Executed complete-module measurements.
verification.json              Executed comparisons and their detailed outcomes.
PROVENANCE.json                 Pinned upstream archive and control hashes.
LICENSE-ProveIt.txt             Inherited MIT No Attribution license.

Source: VladimirReshetnikov/ProveIt, commit
11814771b7490dfbea0ed5fcf0f5b23586334764,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/
ipra_deterministic_opening_2026-11-11.zip.

Fusion of grammar checking with scope checking was already proposed in older
packages, notably deterministic_specialization's scope_fusion supplement.
The contribution here is a smaller realization at the current 780-byte
frontier, using the existing scalar-depth parity and an isolated initial
phase. This is not a new axiom deletion, arithmetic theorem, or proof of an
absolute minimum. The selected program implements the inherited native
calculus and inherits its bi-interpretation unchanged.
