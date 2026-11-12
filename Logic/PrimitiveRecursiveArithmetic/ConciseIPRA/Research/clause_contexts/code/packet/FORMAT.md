# Packet certificate format

This document specifies the input to `checker.py`, the selected standalone
checker. It implements the four-pattern scalar calculus using a goal-directed
packet stream. The checker itself needs only Python's standard library;
`translate.py` and the other supporting scripts are not needed to verify a
certificate.

The implementation and measurements were checked with CPython 3.12.14.

## 1. The outer array

A certificate is a nonempty JSON array:

```text
[packet_0, ..., packet_m, goal]
```

The final item is the closed formula to prove. The preceding items are proof
packets, consumed **from right to left**. There may be no packets: a reflexive
equation needs only its goal.

A successful run prints `ACCEPT` and exits with status zero. Invalid syntax,
an incorrect inference, a scope error, insufficient input, or unused packets
causes rejection with a nonzero exit status. In particular, an otherwise valid
proof cannot carry extra unused packets.

```bash
python3 checker.py < certificate.json
```

The older `{"goal": ..., "proof": ...}` proof-tree envelope is a different
format. Use the supplied translator to convert it.

## 2. Numerical terms

| JSON | Meaning |
|---|---|
| `0` | The numerical constant zero |
| `[t]` | Successor `S(t)` |
| `[n, a, h]` | Iterator `I(n, a; u.h)`; only the body `h` binds `u` |
| Positive integer `j` | The `j`-th innermost enclosing syntactic binder |
| Negative integer `-j` | The `j`-th fresh numerical parameter introduced during checking |

Thus `S(0)` is `[0]`, and the body `S(u)` of an iterator is `[1]`. A raw
iterator `[0, a, h]` is **not a permitted term**: zero-counter iterations are
already contracted to `a`. Whenever opening a binder exposes a zero counter,
the checker performs this contraction recursively.

The current numerical scope equals the number of contextual clauses. At
scope `k`, the available free parameters are `-1, ..., -k`. A supplied witness
has no free positive index; any positive indices in it must be bound inside
that witness. The root scope is zero, so the public goal is closed.

JSON booleans and floating-point numbers are not integer variables or zero.

## 3. Formulas

| JSON | Meaning |
|---|---|
| `[s, t]` | The equation `s = t` |
| `["d", B]` | The paired binder `D(x,y).B` |

The ordinary reading of the paired binder is

```text
D(x,y).B(x,y)  :=  exists x (B(x,0) -> forall y B(x,y)).
```

Inside its matrix, the new variable `y` has index `1` and `x` has index `2`.
An iterator body adds one intervening binder; a nested `D` adds two. The
checker opens binders without capturing indices belonging to a substituted
witness.

For example, `["d", [1, 1]]` denotes `D(x,y).(y = y)`. The bound variable
`x` is unused in this example.

## 4. The initial reflexivity clause

The fixed initial clause is universal reflexivity:

```text
forall y (y = y).
```

Whenever the current goal is a well-formed equation with literally identical
endpoints, the checker instantiates this clause and consumes **no packet**.
This is a representation of the fixed clause, not a claim that reflexivity
has been removed from the theory.

The initial clause is not assigned a contextual index. Contextual index `0`
refers to the first clause introduced by an Open or Close operation.

## 5. The four packet forms

Every packet has exactly two fields, `[b, t]`. Its first field determines the
operation.

### Use: `[j, t]`, where `j` is a nonnegative integer

Select contextual clause `j` and instantiate its one-variable body at the
term `t`. The resulting formula must be the current goal. The checker next
proves that clause's antecedent using the remaining packets.

An unconditional Horn clause is stored internally with the neutral
antecedent `0 = 0`. That antecedent closes automatically, so using an ordinary
local hypothesis needs no extra packet. Conditional clauses introduced by
Open retain their actual antecedents.

### Close: `[-1, t]`

The current goal must be `D(x,y).B(x,y)`, and `t` must be a term at the current
scope. Introduce a fresh parameter `z` and prove

```text
B(t, S(z))
```

under the additional local assumption `B(t, eta)`, where

```text
eta = z   if B is a literal equation and t is the literal integer 0;
eta = 0   otherwise.
```

The new assumption is appended as an unconditional clause whose body does
not depend on its clause variable. The displayed goal and witness are checked
before the scope is extended. All displayed substitutions include zero
contraction.

### Open: `[D(x,y).B, 0]`

If the first field is a `D`-formula, first prove that formula. Then introduce
a fresh parameter `b`, append the conditional clause

```text
B(b,0)  =>  forall y B(b,y),
```

and prove the original current goal with this additional clause. The second
field must be the integer `0`, not `false` or another placeholder. The
original goal was already validated at the outer scope, so the new parameter
cannot escape into it.

### Step: `[E, F]`, where the first field is an equation

First prove `E`, then prove `F`. They must have the shapes

```text
E: I(c, a; u.h)    = t
F: I(S(c), a; u.h) = r.
```

The current goal must be

```text
r = h[t/u].
```

The two iterator sources must share the same counter predecessor, initializer,
and body. At `c = 0`, the first source is the initializer `a`, because zero
iteration is already contracted. Substitution in the conclusion also
contracts any zero-counter iterations it exposes.

## 6. Worked example: `0 = 0`

The complete certificate is:

```json
[
  [0, 0]
]
```

The only array element is the goal. Its endpoints are identical, so the
initial reflexivity clause closes it immediately. No packet is read, and
there is no unused input.

For an executable trace of this example:

```bash
python3 translate.py format <<'JSON'
[[0,0]]
JSON
```

## 7. Worked example: one successor computation

Prove

```text
I(S(0), 0; u.S(u)) = S(0).
```

Put `L = [[0], 0, [1]]`, the encoding of the iterator on the left. A single
Step uses the two reflexive premises

```text
0 = 0,
L = L.
```

The complete certificate has one packet followed by its goal:

```json
[
  [
    [0, 0],
    [
      [[0], 0, [1]],
      [[0], 0, [1]]
    ]
  ],
  [
    [[0], 0, [1]],
    [0]
  ]
]
```

The checker reads the final equation as its goal, then consumes the preceding
packet. Its first field is an equation, so the operation is Step. Both premise
goals close automatically. Here `c = 0`, `a = 0`, `h = [1]`, `t = 0`, and
`r = L`. Opening `[1]` at `0` produces `[0]`, exactly `S(0)`. The resulting
equation is the requested goal, and the packet stream is exhausted.

This example also shows why reflexive premise proofs are omitted from the
stream: they consume no input. Adding explicit records for them would leave
unused packets and cause rejection.

## 8. Reproduce and inspect the supplied examples

Run these commands from the directory containing this document:

```bash
python3 checker.py < examples/induction_uses_hypothesis.json
python3 translate.py format < examples/induction_uses_hypothesis.json
```

The second command displays packets in consumption order, with the current
scope, rule, goal, witnesses, clause indices, and fresh parameters. The
notation `#j` in that trace means bound index `j`; `aj` denotes free parameter
`-j`. The saved trace is
`examples/induction_uses_hypothesis.txt`.

To reconstruct and independently check an explicit proof tree:

```bash
python3 translate.py backward < examples/induction_uses_hypothesis.json > explicit.json
python3 reference/control_recursive.py < explicit.json
python3 translate.py forward < explicit.json > packets.json
python3 checker.py < packets.json
```

The translators validate their inputs and outputs. They are supporting
utilities and do not belong to the trusted packet checker.

The regression and measurement report can be reproduced with:

```bash
python3 test_packets.py
```

The recorded result is `results/verification.json`. Its finite tests support
the implementation review; the structural proof translations and scope
arguments establish the mathematical equivalence of the two presentations.
