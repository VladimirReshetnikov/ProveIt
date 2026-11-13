# Independent review: fixed F-unshift strong and auxiliary conditions

The reviewed `research/ordinary13-f-unshift-fixed-strong-aux-necessary-condition/` gives necessary consequences of a **full standard-natural zero** of the exact F-unshift probe at the fixed compact ports, with J=1, F=0 and C>0. It does not construct or exclude such a zero, or establish a reverse map or Lean/iPRA theorem.

The four actual integer factors multiply to 1, hence each is ±1. For this J=1 slice, q is divisible by 8 and `Delta=a²+4a+3≡3 mod 8`. Exhausting f and I modulo 8 shows the strong factor `1+I²−Delta*(f²−1)` cannot be −1. The main factor is `1+Dstar² mod 4` since U is divisible by 2, and the first factor is `Z² mod 4` because beta is odd and `ell` is divisible by 4. Neither can be −1. The product condition then forces the remaining auxiliary factor to +1. These steps use the literal shifted zeta and fixed q; no sign is assumed for either signed root.

The corrected strict bound uses more than the strong equation. The preceding first/main norm packet gives X>0 and first-Pell index at least 2, so `k≥8M+4` for `M=XY²`. Thus

```text
c=Yk+eta ≥ Y*(8XY²+4) > XY+Y+2 = a+2,
Delta=(a+2)²−1<c².
```

Since the strong equation is `Delta*(f²−1)=c⁴i²` with i≥1, it follows that `f²−1>c²≥c`, hence `f²>c+1`. This depends on the norm-derived k bound; it is not claimed from the strong equation alone.

The auxiliary equation, after setting `I=c²i`, is `(I V)²−(I²−1)y²=1`. Here I>1. The cases y=0 and y=1 are impossible: the first contradicts the equation, while the second forces V=±1, incompatible with `V≡−c mod f²` and `1<c<f²−1`. Standard Pell classification for multiplier I then writes `(I*|V|,y)` as an indexed Pell pair. Its first coordinate modulo I alternates between 0 at odd indices and ±1 at even indices, so the index is odd; y≥2 makes it at least 3. Conversely, an odd index and sign satisfying the stated integral `T≥1` quotient exactly reconstruct the graph's V and auxiliary equation. This is a conditional reformulation for an already chosen strong solution, not a proof that the condition has a solution.

The independent checker pins the exact child rows, reproduces the author's receipt, exhausts the relevant mod-8 and mod-4 signs, and runs bounded controls for the corrected bound, odd Pell index and y=1 exclusion. The uniform arguments above, rather than finite controls, carry the conclusions. The cited classification source and all providers remain unelaborated here; no Lean or build was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-f-unshift-strong-aux-necessary-second-independent/check.py | cmp - reviews/ordinary13-f-unshift-strong-aux-necessary-second-independent/receipt.json
```
