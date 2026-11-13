# Independent review of the coprime-discriminant strengthening

The pinned argument correctly removes the squarefree-discriminant hypothesis under the stated ordinary-integer Pell inputs. For a positive even main index m, `gcd(m,Delta)=1` suffices to reduce every possible same-data parent strong witness to the previously obstructed family. No concrete error was found in the factor extraction, unit classification interface, divisibility, growth comparison, or graph scope. The result remains conditional: it neither supplies such a fixed-port two-norm zero nor excludes parent witnesses with different first/main data.

For `Delta=d*t²` with squarefree `d>1`, the strong equation gives `Delta | I²`. Comparing prime valuations yields `d*t | I`, including primes shared by d and t; writing `I=d*t*u` gives `f²-d*u²=1`. The classification used is that of the least positive **integer-coordinate norm-one Pell solution** `epsilon=X_1+U_1*sqrt(d)`, so all positive integer-coordinate solutions are powers. It must not be replaced without justification by a generator for the full quadratic integer ring, where half-integral coordinates may occur. This standard classification is a mathematical input, not a newly checked Lean theorem.

Writing `A+t*sqrt(d)=epsilon^r` and `f+u*sqrt(d)=epsilon^h` gives `U_(r*m)=t*c`. The already established identity `gcd(c,Delta)=gcd(m,Delta)=1` makes `c` coprime to `d*t`; the actual graph relation `c² | d*t*u` therefore yields `c² | U_h`. The Pell norm gives `gcd(X_j,U_j)=1`; its addition formula and Euclidean reduction prove `gcd(U_j,U_k)=U_gcd(j,k)`. Since c divides `U_h` and `U_(r*m)`, it divides `U_g` for `g=gcd(h,r*m)`.

If g were a proper divisor of `r*m`, then `g≤r*m/2`. Because m is positive and even, doubling gives

```text
c = 2*X_(r*m/2)*U_(r*m/2)/t > U_(r*m/2) ≥ U_g.
```

The strict inequality includes `m=2`: `X_(r*m/2)≥X_r=A>t`, since `A²-d*t²=1` and `d>1`. This contradicts positive c dividing positive `U_g`. Hence `r*m | h`. In particular h is a multiple of r, so the strong witness is `f=x_(h/r)(A)`, `I=Delta*y_(h/r)(A)`. Coprimality of c and t turns `c² | U_h=t*y_(h/r)(A)` into `c² | y_(h/r)(A)`, exactly the previously reviewed obstruction's hypothesis. Both signs of the auxiliary Pell quotient remain excluded there.

The independent checker compares the actual parent unit-factor rows and shared two-norm expressions, verifies the mod-4 exclusion, discovers small integer-coordinate Pell generators independently, checks bounded strong-divisibility and growth/index instances, and reproduces the non-squarefree, nonfundamental `A=2024` illustration. It pins the earlier independent obstruction reviews. These finite controls do not replace the classification, Euclidean and growth proof above. No Lean, build, staging, model transfer, or provider validation was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-parent-even-index-coprime-discriminant-independent/check.py | cmp - reviews/ordinary13-parent-even-index-coprime-discriminant-independent/receipt.json
```
