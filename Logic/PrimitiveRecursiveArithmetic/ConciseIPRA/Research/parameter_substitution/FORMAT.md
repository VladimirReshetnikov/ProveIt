# Raw parameter calculus: standalone checker format

The primary checker is `raw_parameter.py`. It imports only the Python
standard library. It reads one JSON value from standard input, prints
`ACCEPT` and exits zero on success, and otherwise prints `REJECT` and exits
nonzero. The contract concerns the value decoded by Python's `json` module;
duplicate JSON keys have that decoder's ordinary last-value behavior.

The decoded value must be an object with exactly two keys:

```json
{"goal": [0, 0], "proof": ["x", ["c", 0, 0, 1], ["c", 0, 0, 1]]}
```

This example derives reflexivity of zero from a zero computation twice.
There are no public free variables or assumptions. Every supplied public
goal is fully checked as a closed formula. Contexts and fresh parameters
are introduced only inside proof branches.

## Terms and formulas

| JSON value | Meaning |
|---|---|
| `0` | Numerical zero |
| `-1`, `-2`, ... | Rigid free parameters introduced by enclosing branches |
| `1`, `2`, ... | Local bound indices, starting with the innermost binder |
| `[0,t]` | Successor of `t` |
| `[n,a,h]` | `I(n,a;u.h)`, binding the state only in `h` |
| `[s,t]` in formula position | Equality `s=t` |
| `[B]` in formula position | `D_(x,y) B`, binding `y` at index 1 and `x` at index 2 |

Positive integers are variable indices, not numerals. The numeral one is
`[0,0]`; the numeral two is `[0,[0,0]]`. Expected sorts disambiguate the
two-element successor and equality forms.

At a branch scope of `k`, available rigid parameters are `-1` through `-k`.
With `d` surrounding local binders, a numerical leaf must be an exact Python
integer between `-k` and `d`. Booleans and floating-point values are
rejected, even when they compare equal to an integer.

All terms are raw. The checker performs ordinary capture-avoiding
substitution but **no computation normalization**. Computation is justified
by the explicit instruction below.

## Five instruction families

### Computation

`["c", counter, seed, body]`

The complete iterator `[counter,seed,body]` is type- and scope-checked.
The counter must be literally zero or syntactically a successor. The
conclusion is one of:

- `I(0,a;u.h)=a`;
- `I(S n,a;u.h)=h[I(n,a;u.h)/u]`.

A valid counter term that is a variable or another iterator is rejected
by this instruction. Such terms are not syntactic successors.

### Parameter equality

`["x", major, minor]`

The subproofs must derive equations `s=t` and `u=r`. Its conclusion is
`r=Psi(s,t,u)`, where:

1. If `u` is syntactically identical to `s`, `Psi` is `t`.
2. Otherwise, if `s` is a rigid free parameter, `Psi` is ordinary
   simultaneous replacement of that parameter by `t` in `u`.
3. Otherwise, `Psi` is `u`.

Replacement is performed once. Occurrences inside the inserted target are
not revisited. Proper occurrences of zero, successors, or iterator terms
are not replaced by this primitive rule. General congruence is recovered
by the fresh-alias construction in the paper and `translate_raw.py`.

### Clause use

`["u", index, target, premise]`

The index is an exact nonnegative integer selecting a retained clause
`(A; y.B)`. The premise must derive exactly `A`; the result is `B[target/y]`.
The target is checked in the current scope. Contexts are appended, so the
oldest retained clause has index zero.

### Paired elimination

`["e", goal, major, branch]`

The major premise must derive `D_(x,y) B`. A fresh rigid parameter `b` is
introduced, and the branch receives the appended clause
`(B(b,0); y.B(b,y))`. Its result must be exactly `goal`. The goal is checked
before entering the branch, so the new parameter cannot escape.

### Witness-directed paired introduction

`["i", goal, witness, branch]`

The goal must be `D_(x,y) B`. The witness is checked in the original scope.
A fresh parameter `z` is introduced. Put `eta=z` exactly when the matrix
`B` is a literal equation and the witness is literally zero; otherwise put
`eta=0`. Append the ordinary-assumption clause
`(0=0; B(witness,eta))`. The branch must derive
`B(witness,S z)` exactly.

## Generalized opening

The internal operation `opening(tree,value,index)` has two modes:

- Positive `index` opens that bound coordinate, adjusts it under binders,
  and decreases larger bound indices after removing the coordinate.
- Negative `index` replaces that rigid free parameter. It does not change
  bound indices or move its target index under binders.

The default positive index is 1. Opening the outer coordinate of a `D`
matrix uses index 2. Every replacement value supplied by an accepted rule
is locally closed relative to positive indices: it may contain its own
internal binders and negative rigid parameters, but has no dangling
positive index. This invariant is why no extra shifting operation is
needed when that value is inserted beneath another binder. Neither mode
rewrites the structural zero tag of successor.

## Independent utilities

`raw_template_control.py` is the matched control using a one-term transport
template. It has only the positive-index opener it needs; its unused
negative-index machinery was removed for the final comparison.

`translate_raw.py` provides `translate(certificate,to_alias=True)` and its
reverse direction. It verifies each input and replay-checks each output.
It also supports open sequents internally through `forward` and `backward`.
These utilities are untrusted: neither standalone checker imports them.

Run the complete executable validation with:

```sh
python3 verify_raw.py
python3 raw_parameter.py < raw_examples/parameter/passive_source_occurrences.json
```

Python resource limits may reject sufficiently large finite derivations.
The finite validation suite is not a proof-assistant verification of the
checker or the mathematical equivalence.
