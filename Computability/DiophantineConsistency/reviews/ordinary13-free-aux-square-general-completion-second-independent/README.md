# Independent review: general nonsquare auxiliary completion

The reviewed `research/ordinary13-free-aux-square-general-nonsquare-completion/` gives a valid **standard-integer conditional completion** for its 84-row eta/zeta-natural free-y² candidate. For any fixed nonnegative values of the other inputs and ports with `a≥0` and `c>0`, and with the actual signed rank R arbitrary, the four auxiliary inputs can be chosen so that the strong residual is zero, the auxiliary factor is one, and the free y² input is nonsquare. The actual first and main residuals are unchanged. This is not an assertion that those residuals have a common zero, an existential parent-child equivalence, or a Lean/iPRA theorem.

Let `A=a+2≥2`, `Delta=A²−1`. The Pell matrix for multiplier A has determinant one modulo c²; a positive identity period exists, and doubling it makes the period even. Its pair `(f,v)` has v>0 and `c²|v`, with `f²−1=Delta*v²`. Set `i=Delta*(v/c²)` and `I=c²i=Delta*v`. Then i>0, I>1 and `I²=Delta*(f²−1)`. The norm gives `f²≡1 mod c`; the Pell pair modulo A follows `(1,0),(0,1),(−1,0),(0,−1)`, so an even period gives `f≡±1 mod A`. Consequently both `gcd(f²,c)=1` and `gcd(A²,f²)=1`.

CRT supplies a natural starting b with

```text
b*A² ≡ 1+c (mod f²),       b ≡ R+1 (mod c).
```

For `V=1+b*(I²−1)`, the strong equation gives `I²−1≡−A² mod f²`, so `V≡−c mod f²`. Also `I≡0` and `f²≡1 mod c`, so `V+f²R+c≡0 mod c`. The moduli are coprime, so `T=(V+f²R+c)/(f²*c)` is integral and exactly reproduces the literal graph ordinate. Increasing b by `f²c` increases T by the positive integer `I²−1`. Thus T can be made positive even if the actual signed R is negative; then shifted inputs `i−1` and `T−1` are natural.

Set `y2=1+2bI²+b²I²(I²−1)`. The independently checked polynomial identity `(I²−1)*y2=I²*V²−1` makes the free auxiliary factor one. Select a prime p≥5 not dividing `f*c*I*(I²−1)`. As the CRT parameter varies, b ranges over all residues modulo p; y2 is a nondegenerate quadratic with nonzero discriminant `4I²`. Its character sum is ±1, so it has a nonresidue value. Adding multiples of p to the parameter preserves that nonresidue and eventually makes T≥1. Therefore y2 is a nonnegative nonsquare integer.

An independent dependency traversal confirms that `A0`, `A1`, a, c, R and the actual signed main root use none of `n_f,n_i,n_T,n_y2`. It also confirms the same property for the separate [shifted-zeta-parent 84-row candidate](../../research/ordinary13-shifted85-free-aux-square-criterion/README.md). For that shifted variant at nonnegative ports, q≥1, shifted s≥1 and k≥1 make c>0 automatically. Thus **conditionally on any two-norm valuation**, the same construction gives a nonsquare full child zero there as well. Conversely its first and main unit factors cannot be −1 modulo 4, so any standard-integer child zero supplies the two norm equations. This reduces the child-zero question to simultaneous first/main norm existence; it does not supply such a valuation or exclude an existential parent witness replacement.

The checker pins the author packet and both graphs, reproduces the author's receipt, independently traces row dependencies, proves the auxiliary identity as a sparse integer polynomial, and constructs small Pell/CRT/nonsquare controls including c=1 and negative R. The general period, CRT and finite-field arguments above are not established merely by finite controls. No Lean, build, staging, arbitrary-model proof, provider/axiom audit or iPRA endpoint was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-general-completion-second-independent/check.py | cmp - reviews/ordinary13-free-aux-square-general-completion-second-independent/receipt.json
```
