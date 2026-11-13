# A checker for bounded local conversion

`checker.py` is a complete standalone checker for the seven-rule raw-term
presentation in `../ipra_bounded_conversion.tex`. `control.py` is the exact
six-rule weak-head checker from the incoming head-conversion proposal.

The new checker checks **one local iterator contraction at a certificate-selected
counter-spine depth from 0 through 3**. It has no normalizer and does not compare
terms modulo unrestricted computation. It uses literal raw syntax for all other
rules. Every active redex endpoint is validated in full before contraction,
including seed and body parts that a contraction erases.

This is a change of the primitive computation mechanism, not a global
proof-checker-size improvement. With the entire source normalized by CPython
3.12.14 `ast.unparse` and followed by one newline:

| Complete module | Significant tokens | AST nodes | UTF-8 bytes |
|---|---:|---:|---:|
| Six-rule weak-head control | 1060 | 1121 | 3336 |
| Seven-rule bounded-conversion checker | 1075 | 1156 | 3522 |

Docstrings and all input/output handling are counted. The candidate is 186
normalized bytes larger. The mathematical benefit is a uniform bound on the counter-spine
location of each primitive contraction; substitution and validation still
traverse arbitrarily large finite terms. This operational change does not satisfy the requested global
size target.

## Input

Input is one JSON object with exactly four fields:

```json
{"variables": 1, "context": [], "goal": ["=", ["v", 0], ["v", 0]], "proof": null}
```

Terms are `["z"]`, `["v",i]`, `["s",t]`, and `["i",counter,seed,body]`.
The body has one bound variable at index 0, and outer variables are shifted.
Formulas are `["=",left,right]`, `["q",body]`, and `["d",body]`.
For `d`, the matrix indices 0 and 1 bind the counter and witness respectively.
`variables` counts available free numerical parameters, represented by de
Bruijn indices. The context and goal are checked for exact types, syntax and
scope. Proof hints and subproofs are validated when the applicable inference
uses them; an already retained hypothesis or literal reflexive equation needs
no proof payload.

The added inference packet is:

```json
["cv", redex_side_endpoint, depth, branch]
```

Here `depth` is an exact integer in `{0,1,2,3}`. Starting at the supplied raw
endpoint, descend that many iterator **counter** children and contract one
zero or successor redex. The current goal must be an equation whose left
endpoint is either the supplied term or its contracted term. The branch
proves the equation with the other left endpoint and the same right endpoint.
Thus the same instruction supports either direction without a separate bit.
No conversion below a successor, in a seed, in a body, or under a formula
binder is permitted by this primitive instruction.

For example, `fixtures/zero_contraction.json` proves an iterator's zero
computation using one local conversion and reflexivity. The actual equivalence
argument recovers full equality transport and unrestricted computations as
derived rules; the primitive instruction does not itself implement those
larger derived operations.

All other proof tags (`vs`, `qe`, `de`, `di`) retain the control's formats.
The difference is that substitutions are raw and stored formula templates
need not be in normal form.

## Reproduction and evidence

From this `code` directory, run:

```bash
python3 build_transport_packet.py
python3 verify.py
python3 checker.py < fixtures/progress_used_hypothesis.json
```

Acceptance is normal exit with exactly `ACCEPT` followed by a newline.
`verification.json` records measurements and each subprocess result. The
fixtures include nested binders, conversion in both directions at every
permitted depth, rejection at depth 4, a prohibited seed descent, scope/type
attacks in erased hints, simultaneous self-containing substitution, closure
elimination, equation progress using its induction hypothesis, compound case
introduction, and symmetry through a discharged fresh witness.

For each positive raw fixture, an **untrusted producer** erases local conversion
instructions and head-normalizes the stored formulas to make a companion
certificate for the six-rule control. Neither the producer nor the control is
imported by the candidate checker. This comparison verifies examples of the
written interpretation; it does not claim identical raw acceptance languages.

The full symbolic transport fixture proves `s=t, S(s)=r |- r=S(t)`
with three arbitrary free parameters. Its 7,806-byte proof contains 34 local
conversions, including two at depth 3, together with 36 discharges,
36 introductions, 35 variable-substitution steps and three closure
eliminations. `build_transport_packet.py` constructs this fixture using
untrusted named-variable proof generation.

The current suite has 37 fixtures and 116 isolated CLI executions, including
ordinary Python and `python -O`, with zero failed expectations.

Finite runs support the implementation. The universal all-open-sequent
calculus-equivalence theorem remains the written argument; no new Lean or
Rocq certification is claimed.

## Normalization-boundary experiment

From this directory, run `python3 check_normalization_boundary.py` to reproduce 24 additional
CLI executions of the weak-head control on 12 closed terms, in ordinary and
optimized Python. This fixes the context `Q_y B(y)`, the goal `0=1`, and the
proof skeleton `qe(B,t,Hyp,Refl)`, where

`B(y) := I(y,0;u.0) = I(y,0;u.1)`.

The independent numerical evaluator and the control agree in every example:
the certificate is accepted precisely when the supplied closed term has
positive value. The fixed goal is neither a retained hypothesis nor a
reflexive equation, so the initial shortcuts do not bypass the `qe` step.
The context is explicit; deriving `0=1` from it is not an inconsistency of
the checker. The experiment supports the report's separately proved
normalization-boundary reduction. Finite examples do not establish the
universal reduction or a non-primitive-recursiveness theorem.
