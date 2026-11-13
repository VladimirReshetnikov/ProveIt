# Independent review of the 1-mod-4 parent lift

The pinned conditional lift's matrix signs, auxiliary witnesses and literal parent graph bindings check out at source level. Its sufficient assumptions remain open for a general two-norm zero: it requires a main Pell ordinate `c=y_m(A)` with `m≡1 mod 4` and `c | R+m`. This is a standard-integer conditional construction; it is not an unconditional reverse bridge or a Lean/iPRA proof.

There is also a useful **scope strengthening**: the stated evenness assumption on the multiplier `A` is unnecessary for this argument. The inherited general and explicit parent constructions require `A=a+2≥2`, not evenness. For `h=2mc`, h is even, and the Pell doubling identity gives

```text
f=x_h=2*x_(h/2)²-1,
```

so f is odd for every integer A. All subsequent steps in this construction use only that oddness, the inherited strong witness, and the displayed rank congruence. In combination with the separately conditional 3-mod-4 branch, the scalar condition for odd m therefore applies for **either parity of A**, subject to the same explicit graph-zero and congruence assumptions. This observation is an elementary source-level generalization, not a formal Lean theorem.

For the signs, with `B=[[0,Delta*v],[v,0]]` and `f²-Delta*v²=1`, the inherited calculation gives `Q^(2h)≡-Id+2fB mod f²`. Raising to the odd exponent f gives `Q^(2hf)≡-Id mod f²`. Since `L=2hf-m` is positive, this implies `Q^L≡-Q^(-m)` and its lower-left entry is `y_L≡c mod f²`. Also `L≡3 mod 4` and `L≡-m mod c`, so the odd-Chebyshev quotient has `V≡-c mod f²` and `V≡m≡-R mod c`. The rest of the inherited CRT and positivity argument yields integral positive `i,T` and an actual natural square-root input y.

The independent checker pins the construction and graph sources, compares the eight shared graph expression trees and actual parent auxiliary/product rows, tests the period and quotient-index signs for small multipliers of both parities, and checks a complete fact-level auxiliary witness for **odd** `A=3`, `m=1`, `c=1`, `L=67`. This toy is not asserted to be a graph zero. The general parity strengthening follows from doubling and the existing symbolic proof, rather than from the bounded tests alone.

From `Computability/DiophantineConsistency`:

```sh
timeout 20s python3 -I -S -B reviews/ordinary13-shifted-two-norm-parent-odd-index-independent/check.py | cmp - reviews/ordinary13-shifted-two-norm-parent-odd-index-independent/receipt.json
```

The independent checker caps address space, CPU time and core files. No Lean, build, provider audit, model proof, or full graph zero was produced.
