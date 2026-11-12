# Strict canonical R certificate format

`canonical_checker.py` is a self-contained implementation of the six rules in the report. It imports only Python's `json` and `sys` modules. Neither the generator, the tests, nor any certificate file is imported by the checker.

## Public interface

Supply one JSON object on standard input, with exactly the keys `goal` and `proof`. The goal must be a closed canonical native formula. Acceptance is normal exit with status 0 and exactly `ACCEPT\n` on standard output. Rejection is exit status 1 and exactly `REJECT\n`. Exceptions, malformed data, unknown rules, extra rule fields, and unexpected top-level keys reject. No Python certificate data is evaluated. Assertions do not control acceptance.

```
python3 canonical_checker.py < certificates/canonical/used_induction_hypothesis.json
```

The proof format describes all finite derivations of the displayed calculus. Ordinary Python stack, memory, and execution limits can reject sufficiently large valid certificates; these operational limits are not arithmetic axioms or changes of calculus.

## Numerical syntax and scope

At numerical scope `n`, the integer `0` denotes zero and the exact integers `1,...,n` are de Bruijn variables, with `1` the most recently bound variable. Booleans, floats, negative integers, and out-of-scope indices are rejected.

A numerical recursor is `[counter, initializer, body]`. Its counter and initializer have scope `n`; its body has scope `n+1`, where variable `1` is the iteration state and the old variables have increased indices. The body alone binds that state variable.

In canonical R syntax, a term with literal zero counter must have literal zero body. Consequently `[0,a,0]` is the canonical successor `S(a)`. There is no separate successor constructor. A raw node `[0,a,h]` with `h != 0` is rejected in user-supplied syntax, even though the raw recursor would have the same numerical value as `[0,a,0]`.

Internally generated substitution instances use the smart constructor

```
rec(n,a,h) = [n,a,0 if n == 0 else h].
```

Its inputs have already been recursively substituted. Thus a nonzero counter variable that becomes zero under substitution causes its body to be erased at that time. The proof checker does not merely normalize initial input or compare the original counter with zero.

## Formula syntax

| Encoding | Meaning | Body scope |
|---|---|---|
| `['=',s,t]` | Literal equation | Both terms have current scope |
| `['Q',B]` | `B(0) -> forall y B(y)` | Current scope plus 1; `y=1` |
| `['D',B]` | `exists x (B(x,0) -> forall y B(x,y))` | Current scope plus 2; `y=1`, `x=2` |

Root reversal exchanges the two terms of a literal equation and leaves Q and D formulas unchanged. Contexts are reusable ordered lists. Hypothesis index 0 denotes the oldest retained formula. No formula is initially assumed.

## The six proof-tree instructions

All subtree proofs are checked, with the exact scopes and contexts stated below. A rule returns its concluded formula; the public driver compares the result with the submitted goal.

| Instruction | Operation |
|---|---|
| `['h',index]` | Return the indexed retained hypothesis. |
| `['r',n,a,h]` | Conclude `R(S(n),a;u.h) = h[R(n,a;u.h)/u]`. Validate `n,a` at the current scope and `h` at scope plus one. All constructors and substitutions are canonical. |
| `['x',E,p,q]` | Check equation template `E` at scope plus one. Proof `p` must conclude `s=t` with `s` not literally zero. Proof `q` must conclude `E[s]`. Return the root reversal of `E[t]`. |
| `['q',t,p,q]` | Validate numerical `t` at the current scope. Proof `p` must conclude `Q B`; proof `q` must conclude `B[0]`. Return the root reversal of `B[t]`. |
| `['e',A,p,q]` | Validate `A` at the current scope. Proof `p` must conclude `D B`. Check `q` in scope plus one with the old context shifted by one and `Q B` appended. Its conclusion must be the shifted `A`. Return `A`. |
| `['i',A,t,p]` | Validate `A=D B` and witness `t` at the old scope. Introduce a fresh variable `z=1`, shift the old context, and append `B[t,eta]`, where `eta=z` exactly when B is an equation and t is literal zero, and is zero otherwise. Check `p` against `B[t,S(z)]`. Return `A`. |

For X, the additional variable in the template is index 1. The old numerical variables are shifted up by one. Substitution removes that extra variable, decreasing the outer indices again.

For DE, the fresh existential witness becomes variable 1 in the extended scope. In the appended `Q B`, its additional Q binder makes that witness variable 2 inside B. Therefore the original D body B is reused without a substitution traversal. The old retained context and the proposed conclusion are shifted. The proposed conclusion is validated before this extension, preventing the eigenparameter from escaping.

For WI, the matrix B has distinguished variables `y=1,x=2`. Its old free parameters are shifted by one above those two variables; simultaneous substitution then replaces y and x with the selected case/progress term and the shifted witness. The witness is validated before the new variable is made available. This prevents a witness from referring to the future eigenparameter.

## Matched controls

`raw_checker.py` implements the same proof protocol over raw successor-seeded R terms. It does not erase zero-counter bodies and does not impose the canonical-input restriction. Its additional seventh rule is

```
['z',a,h]  concludes R(0,a;u.h) = S(a).
```

`scalar_checker.py` implements the same proof protocol for ordinary initialized scalar I terms, with independent successor `[a]`. Its recursor is `[n,a,h]`; its seventh rule is

```
['z',a,h]  concludes I(0,a;u.h) = a.
```

Its successor rule returns `I(S(n),a;u.h)=h[I(n,a;u.h)/u]`. Its term validator and both numerical traversals have the additional independent-successor case. All other validation, formula manipulation, scopes, rule logic, and input/output behavior are identical across the family.

The three checkers deliberately do not accept identical JSON languages: their arithmetic term grammars and primitive zero equations differ. Their common proof protocols and parallel implementations provide the controlled source-size comparison. The written interpretation theorem relates their mathematical consequence relations.

## Verification boundary

The correctness argument for the code is a structural argument: strict input validation gives well-scoped canonical terms and formulas; shifts and substitutions preserve that invariant; each `derive` branch implements its named inference rule; and the driver checks the resulting closed formula. The test suite includes inference certificates, invalid proofs, scope/capture controls, and independent numerical interpretation checks. It does not establish the universal metatheorem by formal verification, and no Lean or Rocq verification of these new modules is claimed.
