# Independent review of the squarefree same-data obstruction

The stated squarefree strengthening follows from the pinned parent factors and the previously reviewed even-index obstruction. No concrete mathematical or graph-binding defect was found. Its conclusion is conditional: for the same first/main two-norm zero and an even positive index m, it excludes all parent auxiliary choices only when `Delta=A²-1` is squarefree and `gcd(m,Delta)=1`. It does not prove such data exist, that the fixed compact graph meets the hypotheses, or that the two equations have different zero-existence status.

The two shared norm residuals vanish at the assumed data, so the literal parent output gives `Fa*Fs=1`. Both are integers, hence both are `1` or both are `-1`. Here `Fs=1+I²-Delta*(f²-1)`, with `I=c²i`. As `Delta=a²+4a+3` is `0` or `3` modulo 4 and squares are `0` or `1`, `Fs` cannot be `-1`; both factors must be `1`. Shifted `i≥1` and `c>0` make `I>0`, so the strong norm implies `f≥2`.

If squarefree `Delta` divides `I²`, each of its prime factors divides I, hence `I=Delta*v` for a positive integer v. The strong norm becomes `f²-Delta*v²=1`. Standard Pell classification for the fundamental unit `(A,1)` therefore puts this arbitrary strong witness in the form `f=x_h(A)`, `v=y_h(A)` for positive h. This uses ordinary integer Pell classification; the source declaration is pinned, but its model/provider elaboration is not checked here.

Modulo `Delta`, the transition matrix is `A*Id+B` with `B²=0`. Its binomial expansion gives `y_m≡m*A^(m-1) mod Delta`; since `gcd(A,Delta)=1`, it follows that `gcd(c,Delta)=gcd(m,Delta)=1`. The actual graph relation `Delta*v=c²i` then implies `c² | v`. Thus every hypothetical strong witness lies in the family excluded, for both auxiliary signs, by the separately reviewed even-index argument.

For context, squarefreeness itself already forces A even: an odd A makes `A²-1` divisible by 8. This observation does not establish squarefreeness for any actual fixed-port zero.

The independent checker compares the shared graph expression trees and the literal parent factor rows, exhausts the mod-4 cases, tests the gcd formula by modular recurrence, and checks bounded instances of squarefree divisibility and coprime cancellation. The symbolic prime-divisor, matrix and Pell arguments above carry the general claim; finite checks alone do not. The checker pins the reviewed packet and the independently reviewed preceding obstruction.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-parent-even-index-squarefree-independent/check.py | cmp - reviews/ordinary13-parent-even-index-squarefree-independent/receipt.json
```

No Lean, build, staging, axiom inspection, provider audit, model proof or graph zero was produced.
