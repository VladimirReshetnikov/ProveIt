# Independent review: free auxiliary square and a natural main norm

The reviewed `research/ordinary13-free-aux-square-main-norm-nonsquare-partial/` constructs a **partial standard-natural assignment** at the actual fixed symbolic compact ports. Its natural main Pell norm, actual rank, strong residual and auxiliary factor have the stated properties, while the free `n_y2` is nonsquare. The first residual and actual signed main root remain unbound, so this is not a full graph zero or a counterexample to square forcing from all graph factors.

The earlier independently reviewed compact construction provides `R≡3 (mod c)`, positive alpha, and natural eta/zeta coordinates for `c=4Delta+3=4A²−1`, with `A=a+2` and `Delta=A²−1`. The third Pell pair has natural ordinate c and root `g=4A³−3A`, so `g²=1+Delta*c²`. That identity alone does **not** assert that the graph's independently computed signed `Dstar` is `±U*g`.

A positive return of the determinant-one Pell matrix modulo c² supplies a pair `(f,v)` with v>0, c²|v and `f²−1=Delta*v²`. With `i=Delta*(v/c²)` and `I=i*c²`, the actual strong residual is zero, `I≡0 mod c`, and `f²≡1 mod c`.

For `b=4+f²*c*u`, `V=1+b*(I²−1)` and `y2=1+2*b*I²+b²*I²*(I²−1)`, independent polynomial normalization verifies

```text
(I²−1)*y2 = I²*V²−1.
```

Because b≡4 modulo both f² and c, `I²≡−Delta mod f²` gives `V≡−(4Delta+3)=−c mod f²`, while I≡0 and R≡3 give `V+f²R+c≡0 mod c`. The moduli are coprime because f²≡1 mod c. CRT therefore gives a positive integral `T=(V+f²R+c)/(f²c)`, yielding the exact graph ordinate and auxiliary factor one.

Choose a prime p≥5 not dividing the positive integer `f*c*I*(I²−1)`. As u ranges modulo p, b covers the field. The polynomial y2(b) has nonzero leading coefficient `I²*(I²−1)` and discriminant `4I²≠0`. Completing the square and counting solutions to `x²−y²=D≠0` gives the character sum `−chi(leading coefficient)`, so not all values can be squares or zero: a nondegenerate quadratic has at most two zero values, and otherwise the sum would be at least p−2>1. A chosen nonresidue makes y2 nonsquare over the integers.

The checker pins the literal and sources, reproduces the author's receipt, independently verifies the auxiliary polynomial identity and finite-field character controls using explicit residue sets, and constructs two small Pell-period/CRT/nonsquare controls. Those finite controls do not replace the quantified character and CRT arguments above or evaluate the huge compact witness. No Lean, build, staging, provider/axiom validation or iPRA conclusion was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-main-norm-second-independent/check.py | cmp - reviews/ordinary13-free-aux-square-main-norm-second-independent/receipt.json
```
