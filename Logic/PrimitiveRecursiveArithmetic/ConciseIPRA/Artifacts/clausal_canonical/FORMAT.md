# Complete certificate format

The primary module `code/arity_checker.py` is the entire trusted acceptance program. It imports only `json` and `sys`. Certificates, translators, tests, and measurement scripts are not imported by it.

## Input and output

Provide one JSON object with exactly two keys: `goal` and `proof`. The goal must be a closed canonical formula. The context is initially empty and free scope is initially zero. Acceptance requires the derived formula to equal the submitted goal exactly. Acceptance prints `ACCEPT` with exit status 0; rejection prints `REJECT` with exit status 1. Assertions are not used for acceptance. Python resource limits may prevent arbitrarily large finite derivations from being processed.

## Terms and formulas

At free scope `m` and bound depth `d`, exact integers from `-m` to `d` are numerical leaves. Zero is the numerical constant. Negative integers `-1,...,-m` are free parameter names. Positive integers `1,...,d` are de Bruijn indices for bound variables, nearest first. Booleans and floating-point integers reject.

| Array | Sort | Child depths |
|---|---|---|
| `[n,a,h]` | Term `R(n,a;u.h)` | `d,d,d+1` |
| `[s,t]` | Formula `s=t` | `d,d` |
| `[B]` | Formula `D_(x,y) B` | `d+2` |

Inside a paired matrix, `y` is index 1 and `x` is index 2. Only the update body of a recursor binds its state. Every node is strictly validated against its required sort. A zero-counter recursor must have literal zero body. Successor is the abbreviation `[0,a,0]`; one is `[0,0,0]`.

The single `opening(expression, value, depth=0)` operation substitutes a locally closed numerical term for index `depth+1`, lowers greater positive indices by one, and recursively respects the child depths above. It canonicalizes each resulting recursor, including when substitution newly makes its counter zero. The image has no externally free positive index; its bound indices belong only to its own internal recursors. No lifting is therefore required. Negative free levels never change when a branch adds a parameter.

## Context clauses

Each internal context entry is a pair `(A,B)`: an antecedent formula at bound depth zero, and a consequent formula at bound depth one. Its reading is `A -> forall y B(y)`. Context entries are not public formulas. In particular, the generic opener must never be applied to an entire clause pair as if it were an equality: the second component has its extra binder.

Let `c = [[0,0,0],0,0]`, and let `H = [c,0]`. `H` has computation proof `['r',0,0,0]`. An ordinary assumption `F` is stored as `(H,F)`. The same syntax for `F` can be viewed under an unused outer binder because it has no externally free positive index. A hypothesis use is thus `['u',index,0,['r',0,0,0]]`.

## The five instructions

Every instruction below has exactly four entries, including its tag. Context indices count from the oldest retained clause, starting at zero.

| Instruction | Required behavior |
|---|---|
| `['r',n,a,h]` | Validate `n,a` at bound depth zero and `h` at depth one. Return `[R(S(n),a;h), opening(h,R(n,a;h))]`. |
| `['x',h,p,q]` | Validate numerical template `h` at depth one. Check that `p` proves `[s,t]`, and `q` proves `[opening(h,s),r]`. Return `[r,opening(h,t)]`. There is no literal-zero source restriction. |
| `['u',index,t,p]` | Validate the index and term `t`. For context entry `(A,B)`, require `p` to prove `A`; return `opening(B,t)`. |
| `['e',F,p,q]` | Validate `F` at the old scope. Require `p` to prove `[B]`. With fresh `b=-scope-1`, form `C=opening(B,b,1)` and add `(opening(C,0),C)`. Check `q` at scope plus one against the unchanged outer goal `F`. Return `F`. |
| `['i',F,t,p]` | Validate `F=[B]` and witness `t` at the old scope. Put `C=opening(B,t,1)` and fresh `z=-scope-1`. Let `eta=z` exactly when `B` is an equation and `t` is literal zero; otherwise let `eta=0`. Append `(H,opening(C,eta))`. Check `p` at the larger scope against `opening(C,[0,z,0])`. Return `F`. |

The outer goal and introduction witness are checked before the new free level exists. This prevents eigenparameter escape and dependence on a future parameter. The old context is unchanged in a branch. Separate branches may reuse the same next negative level.

## Worked closed certificate

This proves `0=0`: use the same computation `c=0` as both premises of crossed transport with the identity template.

```json
{"goal":[0,0],"proof":["x",1,["r",0,0,0],["r",0,0,0]]}
```

Run it with `python3 code/arity_checker.py < examples/reflexivity.json`.

## Comparison and translation formats

`code/clausal_checker.py` is the same five-rule calculus using explicit `=` and `D` tags and conventional shifted de Bruijn free variables. `code/translate_arity.py` is an untrusted producer for valid tagged clausal certificates. It is not a validator; always validate its input with the source checker when using it as an evidence-producing translation.

`comparison/canonical_checker.py` is the frozen six-rule upstream checker. `comparison/arity_current_control.py` implements that same calculus using the primary checker's variable convention. It has the additional formula `['Q',B]`, whose body binds one variable, a hypothesis rule `['h',index]`, and closure elimination `['q',t,major,base]`. Its transport takes an entire equation template, prohibits literal-zero sources, and reverses the resulting equation; closure elimination reverses an equation conclusion too. The supplied proof translators and regression suite compare these different acceptance interfaces explicitly.
