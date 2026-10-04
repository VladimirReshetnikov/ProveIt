# The 83-operation outer-slack projection accepts every positive input

**Refuted candidate.** Removing one addition from the actual
[84-operation universal source](complete84_scaled_strong_output.md) gives a
complete **83=47M+36A polynomial with 18 strictly positive witnesses and
exact degree 187**. It nevertheless has infinitely many positive zeros at
every positive ordinary input on every inherited valid fixed-program slice.
Thus it cannot represent any such compiled language that omits an input.
The established universal bound remains 84. No conclusion is made about
universality under unrelated, unexplored coefficient recipes.

This is a new transfer of the historical
[weakened-bound collapse](complete75_weakened86_all_input_collapse.md) to the
current seven-factor circuit. Its congruences must be rebuilt: the old
auxiliary target and product signs do not transfer through the later Bezout
projection. The proof below supplies that rebuild. It uses the inherited
Dirichlet and irrational-rotation existence arguments, not a finite search
as a substitute. No huge fixed compiler numerals or full compiler-zero tuple
are claimed to have been materialized.

The [fresh standard-library helper](complete83_outer_slack_collapse.py) and
[receipt](complete83_outer_slack_collapse.json) authenticate the actual source
and proof dependencies as data. They execute no predecessor Python, archived
code, historical builders, or historical suites.

## 1. Exact complete source edit and degree

The parent computes, with `ell=twice_cell_bits=2d`,

```
U=q-F, Q=q-1=(B-1)J,
UminusZ=U-Z,
C=UminusZ-alpha-ell*x,
W=C-Z,
gap=Q*U+UminusZ=q*U-Z.
```

Supply positive `alpha_sum` in place of positive `alpha`. Delete only
`q_minus_FZ`. Replace three retained rows by

```
C_after_alpha = q_minus_F - alpha_sum,
gap_product   = q * q_minus_F,
gap           = gap_product - Z.
```

The computed marker becomes `C=q-F-alpha_sum-ell*x`. Every other row is
unchanged, including the paid input, packing, asymmetric scale, index,
transport, strong and auxiliary factors and the complete finalizer. The
removed row had exactly two consumers. The new source retains all 83 live
rows and every supplied coordinate, with 47 multiplications and 36
additions/subtractions. All six fixed compiler numeral ports and the ordinary
input are unchanged. Signed intermediate registers have no added domain
constraints.

There is the all-ring, complete-output identity

```
P83(alpha_sum,...)=P84(alpha=alpha_sum-Z,...).
```

Every factor agrees under that substitution. The helper proves the equality
inductively through all retained registers, keeping the exact relation
`q=Q+1` until the changed gap expression is identified. The changed private
`gap_product` need not agree by itself. It separately checks the actual
formal finalizer as the product of seven factors minus `Delta`.

The forward map from positive parent tuples is `alpha_sum=alpha+Z`, so every
parent zero gives a positive child zero. The inverse is positive only when
`alpha_sum>Z`. Nothing in the child enforces that restriction. Since this
is an invertible linear substitution of the complete free-coordinate space,
it preserves the parent's uniform exact total degree 187 on each admissible
fixed-program slice. The separate syntactic gate bound remains 197. This
argument does not infer degree from a zero set or a numerical specialization.

## 2. Actual compiler and fixed-minus sign requirements

Write the mathematical Pell base as `A=a+2` and its discriminant as
`Delta=A^2-1`; the source register named `A` is this discriminant.
Let `d,b,DC,DR,MC,MF_native` be the inherited fixed compiler integers, with

```
B=2^d, d positive odd, 3 does not divide d,
b positive odd, MC positive even,
MF_source=MF_native+B-1, K0=DC+B*DR.
```

The actual modified compiler has the stronger power-of-five width and offset
conditions and the original mask construction. None is changed. The
construction uses only the stated parity properties and positivity; it
therefore applies in particular to every valid inherited program slice.

Choose a sufficiently large power of five `N`, and put

```
D_width=d*N, q=B^N, M=q^2-1,
J=(q-1)/(B-1), F=2, alpha_sum=q-2-2d*x,
transport_quotient=1, C=0,
K=q*(q-2)*M+(MC+q*MF_source)*J,
u=2d*x+b.
```

Require `q>2d*x+2` and `q>=16`. All supplied quantities here are positive,
`K` is even, `u>=3` is odd, and `M=3m` with `3` not dividing `m`. The last
claim follows from `v3(4^D_width-1)=1+v3(D_width)=1`.
The current sheared transport factor is already exactly

```
(K0+w)*C+(q-F)-transport_quotient*(q-1)=-1.
```

The new seven-factor circuit must therefore have index factor **−1** when
its four unit norm factors are +1 and its scaled strong factor is `Delta`. Its auxiliary coordinate `T` imposes the
fixed target `R`, not the historical target `R+epsilon-lambda`.
The old family had `lambda=-epsilon` and hence `V+R=-2epsilon (mod c)`;
it cannot be inserted unchanged into `T=(V+c+R*f^2)/(c*f)`.
The rest of this proof uses index sign `epsilon=-1` throughout and target
`R` exactly.

## 3. An even wrap using eight independent signs

For every odd `M>=3` and even integer `K`, there are signs
`omega,t_sign,sigma_sign` and an even integer `j_wrap` such that

```
0<j_wrap<2M,
j_wrap=omega+t_sign*(M*sigma_sign-K) modulo 3M.       (1)
```

All expressions on the right are even, so their even representatives form
classes modulo `6M`. Set `r=M-K+1`. The choices `omega=t_sign=1` and
`sigma_sign=±1`, together with simultaneous negation of `omega,t_sign`,
give `r,r-2M,-r,-r+2M`. Unless `r` is a multiple of `2M`, one representative
lies in `(0,2M)`: inspect its three successive intervals modulo `6M`.
If `r` is a multiple of `2M`, use `omega=-1,t_sign=1` instead. The same
four choices now give the representatives based on `r-2`, which is not a
multiple of `2M`. This proves (1), including the old four-sign exception.
In particular `2<=j_wrap<=2M-2`. No adjustment of the fixed index sign is
used.

## 4. The inherited prime progression and new rho progression

Choose an exponent `e` satisfying

```
e=t_sign modulo 18M, e=t_sign modulo D_width,
e=3 modulo 4, e>=3D_width.
```

The compatible first two congruences have modulus with exactly one factor
of two, so the third is compatible as well. Put `X=2^e`. Then
`q^3` divides `X`, `gcd(X+1,M)=3`, and `v3(X+1)=1`.
The argument in Sections 2–3 of the
[all-input ancestor](complete75_weakened86_all_input_collapse.md) now applies
without alteration: choose `Y=q^3*s` so that

```
A=Y*(X+1)+2=-1 modulo M,
H=4A-5=3*lprime,
lprime prime, lprime=2 modulo 3, lprime>3M, A>M.
```

For clarity, the prime progression uses
`Cprime=4*q^3*(X+1)/3` and
`[q^3*(X+1)/3]*s=-1 (mod m)`. Its first term is a unit at every prime of
its difference; imposing `lprime=2 (mod 3)` preserves coprimality.
Dirichlet's theorem supplies arbitrarily large primes in that progression.
This is an existence step, not a claimed bounded numerical search.

Put `a=A-2`, `E=X*Y`, `P=2X*Y^2+1`, and

```
L=12M*(lprime-1).
```

The exact Pell returns at indices `2M` modulo `M`, 18 modulo 9, and
`lprime-1` modulo `lprime` show that `L` is a Pell-state return modulo
`M*H`, is divisible by four, and is a return period for 2 modulo `H`.
Moreover `gcd(L,M*H)=3M`, and `psi_A(e)=t_sign (mod 3M)`.
These claims use `A=-1 (mod M)`, `A=5 (mod 9)`, and the two eigenvalues
2 and 1/2 modulo `lprime`, as in the pinned proof.

Choose the fixed input Pell index and fields by

```
v=u             if sigma_sign=-1,
v=A*u           if sigma_sign=+1,
kappa=psi_A(v), delta=(kappa-u)/Delta>0,
Fv=chi_A(v)+a*kappa.
```

The standard odd/even discriminant residues make `delta` an integer;
`Fv=sigma_sign (mod 3)`. These fields stay fixed as the main index grows.
For `p=e+L*z`, set `c=psi_A(p)` and define the **new** formulas

```
Numerator=K-omega*p+j_wrap*c-M*Fv,
rho=Numerator/(M*H),
Z=rho*H+Fv,
R=K-M*Z=omega*p-j_wrap*c.                           (2)
```

At `z=0`, (1) makes the numerator divisible by `3M`. Increasing `z`
changes it by `-omega*L` modulo `M*H`. The stated gcd therefore solves
integrality of `rho` by one linear congruence in `z` modulo `lprime`.
Let `p_base=e+L*z0` for a nonnegative solution, and initially use step
`S0=L*lprime`. Then all `p=p_base+S0*r` satisfy (2) integrally and
`p=3 (mod 4)`.

The exponential return gives `2^p=X (mod H)`, and the Pell recurrence
identity `chi_A(p)-a*psi_A(p)=2^p (mod H)` gives integral

```
gamma=(chi_A(p)-a*c-X)/H.
```

Enlarge the progression step to `S=lcm(S0,E,T_E)`, where `T_E` is any
Pell-state return period modulo `E`. Such a period exists because the
Pell matrix is invertible over the finite ring. This freezes both `p`
and `c` modulo `E`. Fix a residue `n0` modulo `E/2` by

```
2*n0=omega*p_base-j_wrap*psi_A(p_base)-1 modulo E.   (3)
```

The right side is even. Since `P=1 (mod E)`, every `n=n0 (mod E/2)`
has `k=2*psi_P(n)=2n (mod E)`. Thus

```
h=(k-R+1)/E                                        (4)
```

is integral and the actual index factor `k-hE-R` is **−1**. This is the
new fixed-minus residue, not the old family's equation with a free linear
factor sign.

## 5. Positive first, main and input coordinates

Take a sufficiently large tail of the `p` progression. The elementary
bounds from the ancestor still apply after deleting its bounded constant
`2epsilon`. For example require

```
c>p+M*Fv+K+M*X+q+2.
```

Then the numerator in (2) is positive and `R<0`. Because
`psi_A(p-1)<c/(2A-1)` and `A>M`,

```
M*gamma*H=M*(2c-psi_A(p-1)-X)
          >(2M-1)*c-M*X > Numerator.
```

Consequently `rho` and the supplied coordinate `sigma=gamma-rho` are
strictly positive integers. Also `Z>0`. The computed input root is

```
W+a*kappa+rho*H = -Z+a*kappa+rho*H = -chi_A(v),
```

so its input norm is exactly +1, despite its negative sign. This root
is a computed register, not a supplied positive coordinate.

The ancestor's irrational-rotation argument applies with the new residue
(3). In detail, for

```
lambda_A=A+sqrt(A^2-1), lambda_P=P+sqrt(P^2-1),
theta=log(lambda_A)/log(lambda_P),
beta=log(sqrt(P^2-1)/(2Y*sqrt(A^2-1)))/log(lambda_P),
h_ratio=log((Y+1)/Y)/log(lambda_P), N0=E/2,
```

one has `1/2<theta<1`. It is irrational: `Delta` is odd, while
`v2(P^2-1)=e+2v2(Y)+2` is odd, so the quadratic fields differ.
Along `p=p_base+S*r`, irrational rotation modulo `N0` enters
`(n0+h_ratio/3,n0+2h_ratio/3)` modulo `N0` infinitely often.
For each sufficiently late hit, `n=floor(p*theta+beta)` satisfies (3).
The inherited exact conjugate-error estimate then yields

```
k*Y<c<k*(Y+1), k=2*psi_P(n), n<p<2n.
```

This is the same estimate as the pinned
[infinite-outer-family proof](complete75_weakened86_infinite_outer_family.md),
for arbitrary fixed positive `Y`. Choose

```
eta=c-k*Y>0, zeta=k*(Y+1)-c>0,
w=X/q>0, s=Y/q^3>0, tau_root=chi_P(n)>0.
```

The new asymmetric scale is exact: `w*q=X`, while the old existence
construction used `X/q^3`. Equation (4) makes `h>0` because `R<0`.
The current first norm is +1 since, with `Lfirst=X*Y^2*k`,
`Lfirst*(Lfirst+k)=(P^2-1)*psi_P(n)^2`. The main norm is +1 by the
chosen `c` and integral `gamma`. Both ratio slacks remain supplied and
positive.

## 6. A positive current auxiliary quotient at the fixed target R

Here `p=3 (mod 4)` and `R=omega*p (mod c)`. Use the normalized
[positive auxiliary lift](complete75_weakened86_auxiliary_sign_lift.md),
with

```
m_aux=p*c, f=chi_A(m_aux), i=psi_A(m_aux)/c^2>0,
S_aux=Delta*psi_A(m_aux)=Delta*i*c^2.
```

The inherited Pell divisibility proof makes `i` an integer. Let the initial
odd auxiliary index be `p` for `omega=+1` or `p+2*m_aux` for `omega=-1`.
It may be increased by any nonnegative multiple of `4*m_aux`. For every
such index `ell_aux`,

```
V=chi_(S_aux)(ell_aux)/S_aux, y_aux=psi_(S_aux)(ell_aux),
V=-c modulo f, V=-omega*p=-R modulo c.
```

The quotient is integral and grows without bound. Choose the index so large
that `V>|R|*f^2+c`, and define the actual new supplied coordinate

```
T=(V+c+R*f^2)/(c*f).                               (5)
```

The numerator is divisible by `f` from `V=-c (mod f)` and by `c` from
`V=-R (mod c)` and `f^2=1 (mod c)`. The normalized strong equation gives
`gcd(c,f)=1`. Thus (5) is integral; the chosen strict inequality makes
it positive. The actual source expression is exactly

```
c*(T*f-1)-R*f^2=V.
```

Therefore the actual auxiliary norm is +1 and the scaled strong factor
is `Delta`. This step supplies precisely the current quotient and does
not assume that the old `R+2epsilon` target was adequate.

All 18 supplied coordinates are now strictly positive integers:

```
J, F, alpha_sum, transport_quotient, f, h, i, T,
s, w, tau_root, eta, zeta, y_aux, Z, delta, rho, sigma.
```

In the current source order the seven factors are exactly

```
(first, main, input, auxiliary, index, transport, scaled strong)
      = (1, 1, 1, 1, -1, -1, Delta).
```

Their fully paid product minus `Delta` is zero. The varying main-index
progression gives infinitely many full positive tuples at every `x>0`.
Moreover `R=K-M*Z<0` forces `Z>K/M>q*(q-2)>q`, whereas
`alpha_sum<q`. The restored parent slack is strictly negative.

No false-language conclusion is drawn merely from that inverse failure:
the all-input theorem is the stronger reason. Applying it to any inherited
compiled proper language, including the pinned
[rejecting compiler recipe](complete75_weakened86_rejecting_compiler.md),
produces positive false-input zeros. This refutes this particular 83-operation
polynomial. It is not a lower bound ruling out other 83-operation constructions.

## 7. Fresh evidence and its limits

The receipt saves the entire 83-row source and its unchanged fixed numeral
interface. An inductive local polynomial checker proves all retained-register
identities and the complete output pullback, with all free ports and all
paid rows live. Another 48 whole-circuit evaluations, 24 rational, compare
all seven factors and the final output with the signed parent image. The
formal actual finalizer is separately checked at seven independent factor
ports. Exact degree follows from the invertible linear source identity;
197 is checked separately as a syntactic upper bound.

The eight-sign lemma is checked at 8,631 even-K cases over 41 odd moduli,
including 123 cases where the old four-sign covering is insufficient.
Twenty-four modular hosts independently check the rebuilt fixed-minus rho
progression, the first-index residue and their preservation along four
further steps. They use the authenticated small `q=2` host as data and
recheck its 60-node Lucas prime certificate. This host is not an admissible
full compiler instance or a full polynomial zero. Six bounded auxiliary
hosts at `A=2,3,4`, `p=3`, both target signs, and large negative `R` fully
materialize `f,i,V,y,T`, checking positive integrality and the two actual
norm factors. Those are complete auxiliary blocks only.

These computations supplement the general prime-progression, rotation,
positivity and Pell arguments. No full compiler witness tuple, huge program
constant, generic search cutoff, or practical universal-zero generator is
claimed. The packet is a bounded data-only CLI, not a public compiler API.

    python3 complete83_outer_slack_collapse.py --root ABS_WIP --expect ABS_JSON
    python3 -O complete83_outer_slack_collapse.py --root ABS_WIP --expect ABS_JSON

Fresh exact receipt replays from `/` passed in both normal and optimized
Python. All checks use explicit exceptions. JSON parsing rejects duplicate
keys and nonfinite values, and receipt comparison preserves types recursively.
