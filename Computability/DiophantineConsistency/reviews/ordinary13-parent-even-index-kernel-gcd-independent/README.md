# Independent review of the kernel-gcd obstruction

The criterion `gcd(c²,d*t) | c` supports the stated even-main-index, same-data parent obstruction. No concrete error was found in its cancellation, subgroup/growth argument, both auxiliary signs or actual parent-factor binding. It is a conditional ordinary-integer statement: it does not construct a compact two-norm zero or exclude different first/main witnesses, and it is not a Lean/iPRA result.

Put `g=gcd(c²,d*t)`. From `c² | d*t*U_h`, cancellation of coprime factors gives `c²/g | U_h`. The hypothesis `g | c` makes `c | c²/g`, so `c | U_h`. For an unrestricted integer U this hypothesis is exactly the condition making that cancellation valid: if `g` does not divide c, `U=c²/g` is a counterexample. This does not assert the criterion is necessary once U is restricted to a Pell sequence.

The previously reviewed Euclidean strong-divisibility and growth proof then applies unchanged, giving `r*m | h` and the positive even A-Pell index `j=h/r`. The strong equation gives `I=Delta*y_j(A)` by positivity. It does **not** generally give `c² | y_j(A)`; the reviewed packet correctly invokes the underlying even-index anti-diagonal argument directly. Its fact-level example `A=2, m=6, c=780, j=1560` verifies this distinction: modulo `c²=608400`, the ordinate is `202800`, while its product by `Delta=3` is zero. It is not a graph zero.

The special cases also follow: squarefree Delta means `t=1`, so squarefree d makes `gcd(c²,d) | c`; and `gcd(m,t)=1` implies `gcd(c,t)=1` through the Pell congruence modulo Delta, leaving the same squarefree d contribution. The packet's `A=8, m=6` example satisfies the criterion with `gcd(m,t)=gcd(m,Delta)=3`, showing these conditions are sufficient examples, not a complete characterization.

There is no need to invoke an odd-prime argument at p=2 in the actual proof: j is even, so `f=x_j=2*x_(j/2)²-1>1` is odd and has an odd prime divisor. For completeness the anti-diagonal contradiction itself also works modulo 2 whenever its matrix hypotheses hold: `Q^u` with an odd vanishing ordinate is scalar identity in that field, whereas an odd power of an invertible anti-diagonal matrix is still anti-diagonal and distinct from identity. Both signs of the auxiliary quotient are covered by the Pell addition identity as in the pinned prior review.

The independent checker pins the new packet, the prior reviews and the actual graph. It verifies the exact cancellation criterion on a bounded grid, its stated special cases, both strict fact-level illustrations, complete modular-state controls including p=2, and the literal auxiliary/product rows. The general proof relies on ordinary integer-coordinate Pell classification, strong divisibility and the algebra displayed above; bounded tests do not replace those arguments or establish model/provider elaboration.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-parent-even-index-kernel-gcd-independent/check.py | cmp - reviews/ordinary13-parent-even-index-kernel-gcd-independent/receipt.json
```

No Lean, build, staging, provider audit, model transfer or iPRA proof was performed.
