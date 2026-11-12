# Goal-directed checker family

These are complete standalone tagged-syntax Python checkers. Each imports only
`json` and `sys`. Run `python3 code/full_checker.py < certificate.json`.
Acceptance means exit status zero and exactly `ACCEPT` followed by a newline.
Exceptions and resource exhaustion are rejection, not acceptance. The mathematical
specification uses unbounded finite trees and the proved terminating normalizer.

## Header and numerical scope

The input is one JSON object with exactly these four keys:

```json
{"variables":0,"context":[],"goal":["=",["z"],["z"]],"proof":null}
```

`variables` is an exact nonnegative Python integer (Boolean aliases are rejected).
`context` is a list of formulas, all in that numerical scope. The goal is validated
before any hypothesis or axiom leaf can close. Every retained context formula is
also validated, including context entries not subsequently used.

The supported constructors are:

| Tree | Meaning | Children and scope |
|---|---|---|
| `["z"]` | zero | no children |
| `["v",i]` | de Bruijn variable | exact integer `0 <= i < scope` |
| `["s",a]` | successor | numerical child in unchanged scope |
| `["i",c,a,h]` | scalar iterator | counter and seed unchanged; body adds variable 0 |
| `["=",s,t]` | equation | two numerical children |
| `["q",B]` | conditional closure | formula child adds one variable |
| `["d",B]` | witnessed closure | formula child adds two variables: y=0, x=1 |

An iterator binds only in its body. All syntax, arity, child sorts and numerical
scopes are checked by one traversal. The `syntax` function additionally checks
that the traversal's normal form is identical to the supplied tree.

The profiles differ only in computational normal forms and automatic axiom
leaves:

| Profile | Permitted iterator counter | Automatic arithmetic/equality leaf |
|---|---|---|
| raw | any term | either primitive iterator computation equation |
| zero | any term other than literal zero | successor computation equation |
| full | a variable or an iterator | reflexive equation `t=t` |

All subterms must satisfy the selected canonical grammar. A zero counter is
normalized to its seed in the zero and full profiles. A successor counter is
also unfolded in the full profile. This normalization is charged as trusted
checker code. The full checker has no primitive computation-equation rule.

The `full_expression` profile changes only the presentation of the same
normalization cases to a conditional expression. It is not a different calculus.

## Proof packets

At each call, the claimed goal is validated first. A retained hypothesis or an
automatic axiom closes without examining the `proof` field; `null` is the standard
leaf spelling. This is ordinary goal-directed proof checking. Ignored proof data
are not claimed to have passed a separate whole-certificate shape validator.

Other packets are:

| Packet | Premises and conclusion |
|---|---|
| `["qe",B,t,p,q]` | `p` checks `Q B`; `q` checks `B[0]`; goal must be `B[t]` |
| `["de",B,p,q]` | `p` checks `D B`; `q` checks the lifted goal with new hypothesis `Q B` and one fresh numerical variable |
| `["di",t,p]` | Goal must be `D B`. After opening witness `t`, `p` checks the successor instance in the extended scope, under the progress assumption for an equation and literal witness zero, and under the zero instance otherwise |
| `["tr",s,t,h,p,q]` | `p` checks `s=t`; `q` checks `h(s)=r`; goal must be `r=h(t)` |

All substitutions normalize according to the selected profile and avoid capture.
The term template `h` is validated in scope `n+1`. The newly bound numerical
variable always has index zero. Adding an eigenvariable shifts every old context
formula; the declared conclusion was checked in the previous scope, preventing
its escape. `de` and `di` put their added assumption at context index zero.
The goal-directed protocol does not need explicit hypothesis indices.

In a full-profile `di`, the witness is already normal. A raw nonliteral zero
witness may become literal zero under normalization; translating an older proof
must therefore use the report's compound-envelope construction when necessary.
The naive translation is included as an expected rejection case.

## Validation and correspondence

The traversal checks the original arity and child sorts before returning a
normal form. It recursively validates all original children before erasing a
redex. Thus `I(0,0;u.v999)` is rejected in scope zero, even though untyped erasure
would discard its invalid body. It also rejects Boolean variable indices, terms
in formula positions, formulas in numerical positions, unknown tags and wrong
arities. A checked source equation or major formula is validated before it can
be used to generate a continuation.

Relative to the stated normal-form calculus, soundness is induction on the
finite accepting call tree. The leaf cases are exactly hypotheses or axioms;
the four packets implement the corresponding primitive rule. Completeness is
induction on a native derivation, passing each major formula or term template
as packet data. These arguments do not rely on the finite regression suite.

`translate_goal.py` is an untrusted format converter. It takes a forward proof
and its forward checker module and reconstructs the explicit major formulas
needed by this protocol. A successful forward-to-goal conversion is replayed by
the standalone target checker; no checker imports this converter.

## Measurements and limitations

`reproduce.py` measures each entire module by `ast.unparse(ast.parse(source))`
plus one LF. It removes no AST node, no docstring and no acceptance code.
Significant-token counts omit only comments and structural whitespace tokens;
AST counts include every node returned by `ast.walk`. Gzip level 9 with timestamp
zero is informational. Source headers are comments, so normalizing naturally
removes them under the same rule used for every profile.

The block-form full normalizer has smaller normalized source than the matched
raw checker, but a larger token count and AST count. The expression form is
three bytes smaller than the matched zero-only checker; it has more tokens and
AST nodes. These are not coordinatewise reductions. The large improvement over
older tagged forward checkers comes from the shared traversal and goal-directed
interface; the compact 516-byte arity checker has a different contract and
remains smaller. No absolute minimum is claimed.

Full normalization can expand terms enormously. Uniform normalization of all
primitive-recursive programs is not primitive recursive. No uniform primitive-
recursive checker bound or internal iPRA proof of the normalizer's totality is
claimed. This is distinct from the written interpretation proof for each finite
term and derivation.
