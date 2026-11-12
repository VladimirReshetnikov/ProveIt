# Complete native scalar uniqueness checker

This is a matched experiment, not a smaller-program claim. `baseline_qi.py`
is the frozen raw eight-rule tagged kernel from the incoming zero-normal
package at repository commit `11be5aabc6b07262046e2553419bc6b05271d178`.
`scalar_ur.py` changes exactly one rule: direct equation-progress
introduction (`qi`) is replaced by scalar uniqueness (`ur`).

Both programs are complete standalone Python modules with the same term,
formula, certificate, scope, context, computation, equality, and logical
interfaces. They import only Python's standard library. They do not import
the test driver, a compiler, or each other.

## Terms and formulas

Terms use de Bruijn indices, with index zero nearest its binder:

* `['v', i]`: a variable; i must be an actual integer in scope.
* `['z']`: zero.
* `['s', t]`: successor.
* `['i', counter, seed, body]`: scalar iteration; only body binds a state.

Formulas are `['=', s, t]`, `['q', B]`, or `['d', B]`.
The Q body binds one numerical variable. The D body binds two; the
closure variable is index zero and the existential witness is index one.

Each input has exactly four keys: `variables` (nonnegative integer),
`context` (list of formulas), `goal` (formula), and `proof` (proof tree).
Normal exit and exactly `ACCEPT` followed by a newline mean acceptance.
Malformed or unsuccessful inputs exit nonzero.

## The uniqueness certificate

`['ur', f, h, t, p]` contains two numerical term templates f and h,
one target t, and one premise proof p.

At ambient numerical scope n:

* f has scope n+1, with index zero its recurrence argument z.
* h has scope n+1, with index zero its previous-state argument u.
* t has scope n; it cannot use the fresh recurrence parameter.
* p is checked at scope n+1 under the original context shifted once.
  No local induction hypothesis is added.
* p must prove `f(Sz)=h(f(z))`.
* The result is `f(t)=I(t,f(0);u.h)`.

Because h's active slot denotes the previous state, it has no extra slot
for z. Every other variable is an original passive parameter. The scoped
syntax implements the usual freshness and counter-independence conditions.

The common primitive rules are Hyp, I0, IS, crossed one-term equality
transport, QE, DE, and DI by cases. The baseline's eighth rule is QI by
equation progress; the new eighth rule is UR. The complete mathematical
equivalence depends on the separate scalar-UR development, not these tests.

## Matched measurements

CPython 3.12.14; normalized source is `ast.unparse(ast.parse(source))+'\n'`.
Significant tokens exclude indentation, newlines, comments, encoding and
end markers. AST nodes include all nodes returned by `ast.walk`.
Gzip uses level 9 and timestamp zero, and is informational.

| Program | Bytes | Tokens | AST nodes | Gzip-9 |
|---|---:|---:|---:|---:|
| Baseline QI | 3322 | 1084 | 1141 | 984 |
| Scalar UR | 3393 | 1124 | 1175 | 1011 |
| Change | +71 | +40 | +34 | +27 |

All syntax validation, binder operations, public input/output, and error
handling are counted. The new rule removes a local induction hypothesis
and equation-root test, but validates more term templates and constructs
a larger conclusion. In this direct implementation the latter costs more.

## Verification

Run `python3 verify.py`. The recorded run has 66 process checks, with
28 expected acceptances and 38 expected rejections, and zero mismatches.
Each case runs under both ordinary Python and `-O`. Cases exercise actual
use of the baseline induction hypothesis, the new rule's lack of one,
fixed contexts, arbitrary target terms, nested iterator binders, capture
attacks, incorrect recurrences, compound/term type mismatches, and exact
integer rather than Boolean scope data.

The example certificates and `validation.json` contain the exact inputs
and outcomes. These finite checks test the implementation; they do not
constitute formal verification or a proof of the UR equivalence theorem.

Python recursion, memory, and other finite host resource limits still
apply, just as in the matched source. The mathematical checker is
understood with unbounded resources.

