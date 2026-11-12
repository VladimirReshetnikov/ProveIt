# One-context equality transport

This directory implements the native scalar calculus from ProveIt commit
`a4e5e96c456303cf231eab2aeeb3291d8889833f`, with one change to its equality
rule. In an arbitrary retained context the new rule is

    s = t, h(s) = u  |-  u = h(t).

Here `h` is one numerical term context. Its hole may be unused. Both `s`
and `t` are unrestricted terms. No new primitive equality-symmetry rule is
needed. The two computation axioms and all five other native rules are
unchanged.

The old transport rule is recovered by exactly two applications:

    a(s) = b(s)  ->  b(s) = a(t)  ->  a(t) = b(t),

using the same major premise `s = t` each time. Conversely, one application
of the old rule with template `h(v) = u`, followed by derived symmetry,
gives the new rule. This proves exact consequence equivalence for all
contexts and all formulas, preserving the existing iPRA interpretations
and both interpretation composites. A proof DAG may share the major;
the supplied JSON proof-tree compiler duplicates it. No linear serialized
proof-size bound is claimed.

## Matched complete checkers

`native_checker.py` and `one_context_checker.py` are both complete
standalone modules. They import only Python's standard `json` and `sys`.
They validate the full statement syntax, contexts, numerical scopes,
all rule parameters, and all fresh-variable subderivations. Their sole
source difference is the transport branch. They do not import the
compiler, a theorem catalog, an axiom database, or a validator helper.
No `assert` statement is an acceptance gate.

`build_checkers.py` and `kernel_common.py.template` reproduce the two
standalone modules but are not needed when running either checker.

The certificate is one JSON object with exactly four fields:

```json
{"variables":0,"context":[],"goal":["=",["z"],["z"]],"proof":[]}
```

The displayed empty proof is a placeholder and is rejected. Working
certificates are under `certificates/`.

Terms are `['v', index]`, `['z']`, `['s', term]`, and
`['i', counter, seed, body]`. Indices are nonnegative de Bruijn indices;
only the iterator body binds a variable. Formulas are `['=', s, t]`,
`['q', B]`, and `['d', B]`. The latter bind one and two variables,
respectively; in `D`, the closure variable has index 0 and the existential
witness has index 1. JSON booleans are rejected as variable counts and
indices.

The proof constructors are:

| Rule | JSON array |
| --- | --- |
| Hypothesis | `['hyp', context_index]` |
| Zero computation | `['zero', seed, body]` |
| Successor computation | `['succ', counter, seed, body]` |
| Native transport | `['tr', a, b, major_proof, minor_proof]` |
| One-context transport | `['tr', h, major_proof, minor_proof]` |
| Closure elimination | `['qe', target, major_proof, base_proof]` |
| Paired elimination | `['de', conclusion, major_proof, fresh_witness_proof]` |
| Paired case introduction | `['di', matrix, witness, step_proof]` |
| Equation progress | `['qi', equation_matrix, step_proof]` |

Acceptance means exit code zero and exactly `ACCEPT` followed by a
newline. Malformed certificates, scope errors, unknown rules, and wrong
conclusions are rejected. Resource exhaustion is not acceptance.

## Reproduction

Run from this directory:

```bash
python3 build_checkers.py
python3 verify.py
python3 one_context_checker.py < certificates/used_hypothesis_induction_one.json
```

`translate.py` is an untrusted compiler in both directions. `verify.py`
checks the output using the independent standalone kernels, exercises
the command-line harness in ordinary and optimized Python, compares
substitution against independent standard-natural-number evaluation,
and regenerates `verification.json` with measurements and outcomes.

The measured complete-module comparison on CPython 3.12.14 is:

| Program | Normalized bytes | Significant tokens | AST nodes | Gzip 9 |
| --- | ---: | ---: | ---: | ---: |
| Native two-context checker | 3,382 | 1,101 | 1,160 | 990 |
| One-context checker | 3,358 | 1,089 | 1,150 | 990 |

Normalization uses `ast.unparse` and one final newline. Tokens exclude
comments, indentation and newline tokens. AST nodes include all nodes
visited by `ast.walk`. Gzip uses level 9 and `mtime=0`. This is a reduction
of 24 bytes, 12 tokens and 10 AST nodes within the same explicit design.
It is not a claim to beat the repository's much smaller compact profiles
or to establish any global minimum.

The receipt records 32 theorem fixtures, 12 negative fixtures, 240 CLI
checks with zero mismatches, and 300 semantic substitution checks with no
budget skips. Positive proofs include an iterator identity whose
induction hypothesis is used, closure elimination, both paired rules,
nested logical binders and iterator binders, open-context transport, and
both derivation translations. Negative checks cover escaping
eigenvariables, an induction-context capture attack, unrestricted
compound induction, incorrect closure bases, forged computations,
malformed syntax and boolean/negative indices. These are finite
implementation regressions, not proof-assistant verification.

## Lean boundary

`OneContext.lean` defines `OPrf`, derives the old transport rule in two
steps, translates every derivation in both directions, and states
`oprf_iff_nprf`. `OneContextBiInterpretation.lean` transfers faithfulness,
both formula round trips, and equiconsistency using the existing native
bridge. Place the two files beside `Native.lean` in the pinned ProveIt
source tree to use its build configuration.

`OneContextOneIntro.lean` independently composes the same equality change
with the existing seven-rule `WPrf` presentation, defines `O7Prf`, and
proves exact equivalence with `WPrf` and the native kernel. Its introduction
starts at the fresh variable exactly when the matrix is a literal equation
and the witness is literally zero; otherwise it starts at zero. It does
not change the existing witness-dispatch convention. This optional
composition preserves the seven-rule count. No separate checker or
checker-size measurements are claimed for it. The report-ready fragment
`seven_rule_subsection.tex` states its complete introduction schema and
proof dependencies.

These Lean files were checked against the pinned declaration names and
reviewed independently, but **they have not been compiled**: this
environment has no Lean or Lake executable. They contain no `sorry` or
added axiom. Source text without a successful Lean build is not described
as machine verification.
