# Growing resonant selectors with unchanged odd-scale completion

For each fixed authentic original compiler, the fixed-prime construction admits selectors on its existing plus or minus subsequence of the form

```
z=z_A+A*h_sel,
h_sel -> infinity,
log(h_sel)/log(Q) -> 0.
```

All exact odd-prime denominator depths, forced fixed-prime quotient carries, positive outer/input coordinates and the completed odd scale `A^3 | Y` are retained. The selector and `F=Kz` still obey the upper bound `Q^(1+o(1))`. Here `h_sel` is a mathematical quotient, not the existing native witness named h, a new supplied coordinate, or an uncharged circuit operation.

This note does not prove the binary population condition or assert a complete positive83 source zero. No row, gate, witness interface, universal bound or compiler recipe is changed. Root proposed the exact selector residues and a shifted coprime search; the proof below verifies these and the three-adic growth mechanism. Subsequent binary arguments must be proved separately.

## 1. Fixed source and inherited construction

Fix one authentic original powers-of-five compiler. Write

```
B=2^d, m=B-1, D=dn, Q=B^n, rep=(Q-1)/m,
Dmask=m-MC, K=DC+B*DR.
```

The source coefficient K is distinguished from any native coefficient bearing a similar name. The compiler has d a power of five with d>=25, and its literal mask satisfies `MC` positive and even, `MC<m`, hence `0<Dmask<m`. The source MF is the shifted coefficient used by the actual83 packing, not the native MF before the shift.

The shape is selected once from the fixed value of K, exactly as in the accepted source-coupled construction:

| Shape | q | A=odd(q) | t=v2(q) | T | ell=2dT | tau_p |
|---|---|---|---|---|---|---|
| plus, K!=3 modulo5 | Q(Q+1)/2 | Q+1 | D-1 | n(D-1) | 2D(D-1) | v_p(D-1) |
| minus, K=3 modulo5 | Q(2Q-1) | 2Q-1 | D | n(D+1) | 2D(D+1) | v_p(D) |

Here p ranges over the odd primes dividing A. In both cases `5` does not divide A and

```
J=(q-1)/m,
Z=C=z, F=Kz, W=0,
A0=q^2(q^2-1)+(MC+q*MF)J,
G0=(1+qK)(q^2-1),
R(z)=A0-G0*z, r=(R-1)/2.                         (1)
```

These are the actual packed-index identities: the source gap simplifies to `q^2-z-qF`. The helper authenticates the complete83 JSON and guards the13 literal rows from its repunit through `r_lhs`; it does not execute the array.

The fixed-prime subsequences, using j>=1 only as a subsequence index here, are

```
plus:  n=9^j, S={primes dividing B+1}, A_S=(B+1)n;
minus: v=9^(phi(d)*j), n=((d+1)v-1)/d,
       S={primes dividing 2B-1}, A_S=(2B-1)v.     (2)
```

For minus, phi(d)=4d/5, so Euler's congruence gives v=1 modulo d; also n=1 modulo4. Both branches have n=1 modulo4 and the same fixed finite prime set S throughout their respective subsequence. The complete S-supported part of A is A_S. As proved in the fixed-prime note,

```
Bn<A_S<=(2B-1)n.                                 (3)
```

For `p^a_p || A`, put

```
b_p=a_p+tau_p=v_p(2^ell-1),
g=product_(p|A) p^tau_p <=D+1,
e_p=max(1,2a_p-tau_p) for p in S,
Cextra=product_(p in S) p^e_p <=A_S^2,
N=A_out=A/A_S,
m0=4d (plus), m0=4d/5 (minus),
M=m0*A*g*Cextra.                                  (4)
```

The inherited source class modulo m0 forces z=1 modulo4 and R=b modulo2d, where b is the compiler's inner exponent. In particular R is odd with R=3 modulo4. CRT yields a least positive `z0<=M` in that class satisfying

```
R(z0)+1 = -2p^b_p modulo p^(b_p+e_p)  (p in S),
R(z0)+1 = 0 modulo p^b_p             (p|A, p not in S).  (5)
```

The factor2 is essential because `r+1=(R+1)/2`. All divisibility arguments may initially use signed R. Positivity is established in Section5 before applying a positive-quotient carry theorem.

## 2. Exact least positive residue modulo A

The conditions(5) imply A divides R+1. Conversely, the following calculation determines precisely which residue of z this divisibility forces, independently of the higher conditions. Since q is divisible by A, (1) gives

```
R = MC*J+z modulo A,
mJ = -1 modulo A.
```

Also gcd(m,A)=1: in the plus shape A=2 modulo m, and in the minus shape A=1 modulo m, while m is odd. Thus

```
A | (R+1)  iff  m*z = MC-m = -Dmask modulo A.    (6)
```

Its least positive representative is

```
plus:  z_A=1+(m-MC/2)*rep=Q-(MC/2)*rep;
minus: z_A=2Dmask*rep.                            (7)
```

For plus, `m*z_A = mQ-(MC/2)(Q-1)` becomes `-m+MC=-Dmask` modulo Q+1. The evenness of MC makes this an integer identity without dividing a congruence by2. The bounds `0<MC<m` give `1<z_A<Q<A`. For minus,

`m*z_A=2Dmask(Q-1)=-Dmask modulo 2Q-1`,

and `0<z_A<2(Q-1)<A`. Therefore (7) really supplies the unique representative in `[1,A-1]` in each shape.

Every positive resonant selector consequently has the unique expression

```
z=z_A+A*h_sel, h_sel a nonnegative integer.       (8)
```

In particular, since M is divisible by A, `z0=z_A+A*h0` for an integer h0>=0.

## 3. A shifted coprime search forces growth

Let L(1)=1 and, for N>1, define

```
L(N)=floor(2^omega(N)*N/phi(N))+1.                 (9)
```

If beta is a unit modulo N, every interval of L(N) consecutive integers j contains a j with `gcd(alpha+beta*j,N)=1`. For completeness, inclusion-exclusion counts these j as `L*phi(N)/N+E`, where `|E|<2^omega(N)`. The defining strict inequality in(9) makes the count positive. The proof is translation invariant, and N=1 is immediate.

Along `z=z0+M*j`, every condition(5) and the source class are preserved, and

```
(r+1)/(Ag)=eta0-(G0*m0*Cextra/2)*j.               (10)
```

The slope is an integer and is a unit at every prime dividing N: such a prime divides neither G0, m0 nor Cextra. No unit assertion at S is needed or made. Choose a successful j in the shifted interval

```
1<=j<=L(N),                                      (11)
```

rather than an interval starting at zero. Then the remaining exact depths are recovered, and

```
v_p(r+1)=b_p for every p|A,
M<z<=M(L+1)<=2ML,
h_sel=h0+(M/A)j >= M/A = m0*g*Cextra,
h_sel < 2m0*g*Cextra*L(N).                        (12)
```

The last strict inequality follows from z<=2ML and z_A>0. These conclusions also hold when N=1, where j=1 works. The shift does not claim to keep the old numerical selector bound unchanged; the explicit factor2 is carried into the positivity threshold below.

## 4. A quadratic lower bound from the fixed prime3

Because d is odd, 3 divides B+1 and also 2B-1, so 3 belongs to S in both shapes.

For plus, n=9^j is divisible by3. Hence `tau_3=v3(D-1)=0`, while odd-prime lifting gives

```
a_3=v3(B+1)+v3(n), 3^a_3=3^v3(B+1)*n>=3n.
```

Thus e_3=2a_3 and `Cextra>=3^e_3>=9n^2`.

For minus, v=9^(phi(d)*j) is divisible by3 and `D+1=(d+1)v`. Therefore `tau_3=v3(D)=0`. Since `A=(2B)^v-1`,

```
a_3=v3(2B-1)+v3(v), 3^a_3>=3v,
e_3=2a_3, Cextra>=9v^2.
```

Here `v=(dn+1)/(d+1)>=dn/(d+1)`. In either shape, (12) therefore gives the explicit uniform lower bound

```
h_sel >= 9m0*(d/(d+1))^2*n^2.                    (13)
```

We used only g>=1 to write(13). In particular h_sel tends to infinity along the entire relevant subsequence of sufficiently large parameters for which we make the shifted choice. This lower bound holds for every successful j in(11), not just a specially selected successful representative.

## 5. The doubled explicit bound still preserves positive completion

Since N is odd and5-free, the elementary factor estimate

`phi(N)/(2^omega(N)*sqrt(N))>=1/sqrt(3)`

gives `L(N)<=floor(sqrt(3N))+1`, including N=1. With (3)-(4), A<2Q and g<=(d+1)n, define the inherited bound

```
Zbound=8d(d+1)(2B-1)^2*n^3*Q*(floor(sqrt(6Q))+1).
```

It bounds ML, so (12) yields `z<=2Zbound`. The sufficient positivity condition for this shifted construction is explicitly

```
(K+2)*2Zbound + 2d*(5n+T) < q/2.                 (14)
```

This is the old displayed threshold with the selector term doubled; the old threshold alone is not invoked. For each fixed compiler, the left side is `O(n^3 Q^(3/2))+O(n^2)`, whereas q>=Q^2/2. Thus every sufficiently large parameter on either unbounded subsequence satisfies(14). Checking(14) is a finite mathematical parameter test, not a claim that a first passing value certifies all later values or that its computation is free in the source circuit.

Choose x0 in `[5n,5n+T-1]` in the required class `(R-b)/(2d)` modulo T, and put

```
S0=q-(K+2)z-2dx0,
x(k)=x0+kT, u(k)=2dx(k)+b,
alpha(k)=S0-ell*k.
```

Equation(14) gives S0>q/2. The exact positive interval remains `0<=k<=floor((S0-1)/ell)`. The accepted source-coupled proof applies to these enlarged z using this actual positive slack, not an assumption z<=4d. It yields the unchanged index bounds, period divisibility and transport:

```
3q+1<R<q^4-q^3,
10D+b<=u(k)<2q<R,
R-u(k)=0 modulo ell,
X(k)=2^R-2^u(k)>0,
q(q-1)|X(k), transport=1+z*(X(k)/q)/(q-1)>0.
```

In particular r and all quotients in(5) are now positive. The fixed-prime carry identity gives `c_p=v_p(binomial(2r,r))>=b_p+e_p>=3a_p` at S, and `c_p>=b_p>=a_p` outside S. Consequently the inherited odd-prime input modulus satisfies

```
Hreq=product_(p|A) p^max(3a_p-c_p,0) <= A_out^2.
```

The unmodified fixed-prime estimate `A_S^2>6ell`, together with q>=A^2/3, gives

`ell*Hreq < A^2/6 <= q/2 < S0`.

Thus every representative `0<=k<Hreq` fits the positive interval. The accepted all-precision input isometries and CRT then choose a k for which

```
A^3 | Y, Y=M_r(X)/2.                             (15)
```

All odd-scale conclusions of the fixed-prime construction are therefore preserved by (11). The ordinary input is constructed and may depend on the chosen selector; it is not a prescribed input. No binary population result is used in deriving (15).

## 6. The upper bound remains subpower

For every epsilon>0 the exact product

`2^omega(N)*N/phi(N)=product_(p|N) 2p/(p-1)`

is at most `C_epsilon*N^epsilon`: absorb the finitely many primes below a fixed cutoff into the constant and bound each remaining factor by p^epsilon. The same bound with an additional1 holds for L(N). This is the accepted subpower estimate, and does not require a distributional theorem about primes.

Since N<=A<2Q, g<=(d+1)n and Cextra<=(2B-1)^2*n^2, (12) gives, for every epsilon>0,

```
h_sel <= C'_epsilon*n^3*Q^epsilon.               (16)
```

For every delta>0 choose epsilon=delta/2; the fixed constant and n^3 are eventually at most Q^(delta/2), since Q=B^n. Therefore `h_sel<=Q^delta` eventually. Combining this with (13) proves

```
h_sel -> infinity, log(h_sel)/log(Q) -> 0.
```

Likewise `z<=2ML` gives `z<=Q^(1+delta)` and `F=Kz<=Q^(1+delta)` eventually for each delta>0. These are upper bounds for z and F; no claim z/Q tends to1 is made.

## 7. Exact scope, dependencies and fresh evidence

The following files were read as inert mathematical text or JSON and authenticated by the fresh companion. Their compiler/native/Pell ancestors remain inherited at their accepted scopes.

| File | SHA256 |
|---|---|
| complete83_fixed_prime_quotient_carries.md | 53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46 |
| complete83_subpower_selector_bound.md | 3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4 |
| complete83_source_coupled_input_lifting.md | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |
| complete83_nondyadic_outer_family.md | 42281ee2c1cf99851d4fe67fcfe6f61322fd721d8ebd8ec539983a6edcc44d23 |
| complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |
| complete75_half_binomial_compiler.md | 68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117 |

The first four mathematical notes were read in full for this construction or their earlier author/review work. The compiler note's opening through Section1 (lines1-125) was reread for the fixed powers-of-five layout and literal mask bounds; no new full compiler audit is claimed. The complete83 JSON is authenticated, with13 source-interface rows checked literally, but never executed.

Fresh standard-library finite evidence comprises36 exact canonical-residue/affine-packing cases with relaxed fixed numerals,6,582 shifted coprime-interval cases,2,592 representative endpoint bounds, and18 modular three-adic growth cases. The relaxed d=5 cases in the evidence are arithmetic diagnostics, not authentic compiler slices; the theorem retains its stated authentic-domain hypotheses. The residue examples are not full source instances. The three-adic checks use modular exponentiation and do not materialize Q, X, Y or enormous Pell coordinates. These finite checks corroborate the identities; the all-parameter claims are proved above.

No supplied, archived, committed, frozen or copied predecessor program was executed or imported. No full source array was evaluated, and no actual compiler zero was materialized. The separate binary condition `popcount(R)>=3v2(q)+2` is not proved by this packet. A conclusion about complete83 zeros, semantic soundness, an ordinary integer compiler, or a new operation bound requires additional arguments.

Fresh writer and normal/optimized exact receipt checks passed from `/` before freeze.

Final helper SHA256: `62f3a6750357f593f809f74fad63fae4fb7b716dc28a36333a32898f7b802d57`.

Final receipt SHA256: `141d51917d28d4ead733e722f0e466383d780ca130cb09222273d7f531e36718`.
