# Independent review: modulo-31 same-witness auxiliary obstruction

The [reviewed construction](../../research/ordinary13-shifted-free-aux-odd-index-31-obstruction/README.md) correctly exhibits fixed-compact partial data for which the chosen even-period strong witness has no same-data odd-index parent auxiliary completion. I found no mismatch in the even-period divisibility, modulo-31 sequences or signed main-root obstruction. These partial data are **not a two-norm child zero**, and the result does not refute a different strong witness, another coordinate-changing reverse map or existential equivalence.

With shifted zeta, `J=w=1`, `s=31`, eta=4 and `n_zeta=2q−3`, the exact graph has `k=2(q+1)` and `c=Yk+eta=2A=y₂(A)` for `A=Y(q+1)+2`. All stated inputs are natural at the fixed q. For `z_j=y_(2j)(A)`, the two-step recurrence reduces modulo 4A² to `z_(j+2)=−2z_(j+1)−z_j`; with z₀=0, z₁=2A, induction gives `z_j≡(−1)^(j−1)2Aj`. At j=2A this gives c²=4A² dividing y_(4A), so the chosen h=4A is an even, valid strong Pell index and i is natural and positive.

Because s=31, A≡2 mod 31; because the fixed q is divisible by 8, A≡2 mod 8 and h≡8 mod 32. Direct independent matrix iteration at multiplier 2 gives `(x₈,y₈)=(0,14)` and `(x₃₂,y₃₂)=(1,0)` mod 31, so 31|f. The strong identity gives `I²≡−3≡28 mod 31`; its only two square roots are 11 and 20. Directly iterating the odd quotients for **both** roots gives the 16-periodic set `{±1,±3,±8,±15}`. Since c≡4 mod 31, neither sign can satisfy the necessary `epsilon*x_ell(I)/I+c≡0 mod f²`. This checks only the selected f/i and same remaining data, not all possible strong witnesses.

For the actual signed main root, `U=31q⁵` and `H=4Y(q+1)+3` are coprime: H is odd and H≡3 mod 31. A main residual zero would make d=Dstar/U an integer, and the root formula would give `d−ac≡q mod H`. Its norm forces d=±x₂(A). The exact identity `x₂−a*c=H+4` makes the positive sign require H|(q−4); the conjugate norm makes the negative sign require H|(4q+1). Both integers are positive and smaller than H at the fixed q. Thus the partial data cannot satisfy the actual signed main equation, despite having c=y₂. This is why the obstruction does not supply a counterexample among two-norm zeros.

The receipt reproduces the author checker, pins the shifted graph and reverse-criterion source, and independently iterates both modulo-31 roots, bounded even-subsequence cases and fixed-exponent analogues. Those finite controls supplement the stated induction and divisibility proof. No fixed giant Pell value, Lean process, provider/axiom validation, global parent/child inequivalence or PDF claim was made. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-shifted-free-aux-odd-index-31-independent/check.py | cmp - reviews/ordinary13-shifted-free-aux-odd-index-31-independent/receipt.json
```
