# Independent mathematical review of the dyadic ten-positive construction

Reviewer scope: the new weighted-radical extraction, its place before the
positivity and transport arguments, removal of the factor `mu` from `I`, and
canonical completeness of the three-centered carrier. The literal circuit
`circuit.py` and the complete upstream proof at commit
`ec80841c07e91be8956ce6ed4af9a9c0b782d3d9`,
`Computability/DiophantineConsistency/candidates/ten-positive-scaled-norm/PROOF.md`,
were inspected independently. This review does not claim a new audit of the
upstream native compiler or K215-to-ZFC calibration, and does not certify a
Lean derivation.

## 1. Weighted square classes: accepted

Let `r_j>0` have rational squares with 2-adic valuation zero. Assume the
weights are distinct powers of two, and a signed weighted sum is rational.
Group the roots by their nonzero rational square classes. If `r_i,r_j` are
in the same group, their ratio is rational and its 2-adic valuation is zero.
In a fixed group, divide a putative zero signed sum by one of its roots.
The resulting rational summands have pairwise distinct 2-adic valuations.
Clear their odd denominators and divide by the lowest power of two. Exactly
one remaining summand is odd, a contradiction. Thus no square-class group
can have a vanishing signed weighted sum.

In the finite multiquadratic splitting field, project the asserted rational
linear combination onto any nontrivial sign character by averaging over the
Galois group. This gives exactly a vanishing weighted sum over one nontrivial
square-class group, which was just excluded. Every represented character is
therefore trivial, and every root is rational.

This proof does not require the roots to have any particular Archimedean
order or relative sizes. It uses ratios of roots only within a common
square class; it never assigns a rational valuation to a general irrational
root. The argument works just as well with any fixed distinct nonnegative
exponents in the powers of two.

For the supplied construction, `q` is even, `mu=q^2+1` is odd,
`lambda=2*mu`, and `A=lambda*(a+2)+1` is odd. Consequently `Delta=A^2-1`
is even, `V0=X*lambda^2*Y^2` is even, and all of

```
Dtau, Df, Dnum, delta, Dmain, H
```

are odd. The four unweighted root squares are

```
Dtau, Df, Dnum/delta, Dmain/H^2.
```

They all have 2-adic valuation zero. The weights of `(y,f,tau,d)` are
`(1,2,4,8)`, so the lemma applies without any congruence on the unknowns
beyond their stipulated positive-integral domain.

## 2. Bootstrap and absence of circularity: accepted

Before assuming the norm equation, `k>=2`, `c=kY+eta>=3`, and `I=ic^2>=9`.
Thus `Delta>0`, `Q=Delta^2 I^2>1`, and `Df-c>=2`. Put
`b=c(T+alpha)-R`. If `b=0`, then `V=-c`, so `|V|>=3`. If `b!=0`,
integrality gives `|V|>=Df-c>=2`. In both cases `Dnum=QV^2-1>0`.
Therefore every root used in the norm factorization is a positive real
number before any use of transport, the index congruence, or `V>0`.

After the norm vanishes, the weighted character argument proves all roots
rational. The roots of the integer radicands are integers. Apply the
adjacent-coefficient descent to `abs(V)` to show that `y` is an integer;
this application does not assume the later conclusion `V>0`.

The first and main Pell classifications then give the early lower bound on
`c`. The case of first index one would force `k=2`, `eta=zeta=1`, and
`c=2Y+1`; this lies strictly between the first two possible main-Pell
ordinates, so it is impossible. The first index is at least two, giving
`c>8q^5` (the new factor two in `lambda` actually strengthens this bound).
Combining this with the upstream bound

```
R < q^4 + (alpha+2)q^2
```

proves `c(T+alpha)>R`, hence `b>=1`, `V>0`, and `y>V`.
No consequence of `Bt>=0` was used to prove these facts.

## 3. The new transport bound: accepted

Write `Cf=AI`, `Ct=V0*k`, `u=y-V`, `s=Y/q^3`, and
`g=(epsilon_d*Dm-X-(A-2)c)/H`. At this stage `s` is only known to be a
positive rational. With either sign of the corresponding roots,

```
epsilon_f*f-Cf < 0,
epsilon_tau*tau-Ct < k,
epsilon_y*y-V <= u,
8g < k.
```

For the last bound, use `Dm<Ac`, hence `g<2c/H`, together with
`c<2kY` and `H>32Y`. This is an upper bound and does not require `g`
to be nonnegative.

The global majorant

```
|R| < q^4 + F*q^3 + (alpha+2)q^2
```

holds before transport even when `R` is negative. Since `mu^2>q^4` and
`Delta>mu^2`, it gives

```
|rho| < k+F+alpha+1,  where rho=(k-R-1)/mu^2,
u < b/Delta < k*(T+alpha)+F+alpha+1.
```

The gap estimate follows from

```
u = (V^2-1)/((Q-1)(y+V)) < Df*b/(2(Q-1)) < b/Delta;
```

the final strict inequality uses `Delta+2<Delta^2 I^2`, satisfied here.
If `Bt<=-1`, then `W*Bt/(q-1)<-L`, and the carrier equation forces

```
n < k*(T+alpha)+6k+2F+2alpha+2-L < 0,
L = (k+F+1)*(T+alpha+6).
```

Indeed the difference between `L` and the preceding positive bound is
`(F+1)(T+alpha)+4F+4-2alpha>0`, using `F,T,alpha>=1`.
This contradicts `n>=1`, so `Bt>=0` follows without an unproved sign
assumption. The subsequent outer bound on `R` is consequently available.

## 4. Index extraction and the factor eight: accepted with explicit cancellation

The denominator of the index term remains `mu^2`, not `lambda^2`.
It is coprime to `q^3(q-1)H`: `q` is even, `mu=q^2+1` is odd, and
`H=8mu(a+2)-1` is `-1` modulo every prime dividing `mu`.
Thus rational integrality of the signed root sum still implies
`mu^2 | k-R-1`. Also `mu^2 | 4V0`, preserving the first-index congruence.

The weighted main projection yields

```
H | 8*q^3*(q-1)*(X+(A-2)c-epsilon_d*Dm).
```

Because `H` is odd, the factor eight cancels. The upstream Archimedean
argument fixing `epsilon_d=+1` and `X=2^R` therefore applies to exactly
the same divisibility statement as before. Once this is established,
`g` is an integer, and the remaining two denominator extractions give
`q^3 | Y` and `q-1 | Bt` as in the parent proof.

Removing `mu` from `I=ic^2` does not affect the rank or index lemmas:
they require `c^2 | I`, not the stronger old condition `mu*c^2 | I`.
The first-Pell parameter and main-Pell parameter use the same
`lambda`, so the inherited ratio lemma applies verbatim with that value.

## 5. Canonical completeness and the positive n variable: accepted

Choose the strong index `m=R*c`. For `c=psi_A(R)`, the multiplication
formula

```
psi_A(R*c)=c*psi_Dm(c)
```

and the standard congruence for `psi_Dm(c)` show that this number is
divisible by `c^2`. Thus `i=psi_A(R*c)/c^2` is a positive integer and
the proposed weaker strong ordinate is constructively available.

Let `S=Delta*I` and `Q=S^2`. The inherited auxiliary lemma supplies
`V=chi_S(R)/S`, `y=psi_S(R)`, and `u=y-V>0`. The canonical source has
`R=3 mod 4`, `R>3q`, so `v=(R-1)/2>=2`. Its polynomial recurrence gives

```
V >= (3Q)^v >= 9Q^2.
```

Since `V>=2`, `Q>=3`, and `V<y<2V`,

```
u = (V^2-1)/((Q-1)(y+V)) > V/(4Q)
  >= 9S^2/4 > 3S+1 > 2I+Y+1.
```

Here `I>Y` and `S>I` follow directly from `I=ic^2`, `c>kY`, and
`Delta>1`. The offset auxiliary parameter is available as well:

```
Tstar=(V+c+R*Df)/(c*Df) > V/(c*Df) > 9S > alpha,
```

using `c<S`, `Df<Q`, canonical `R>0`, and `alpha<q<S`. Hence
`T=Tstar-alpha>=1`.

Finally choose

```
n = W*t + rho + 8g + 4(tau-Ct) + 2(f-Cf) + u - s.
```

All quantities are integers in the canonical reconstruction. The terms
`Wt,rho,g,tau-Ct` have the asserted nonnegative or positive signs, whereas
`f-Cf>-I` and `s<=Y`. Thus the strict lower bound on `u` gives `n>1`.
The all-positive sign factor of the norm then vanishes. In particular,
centering at `AI`, which lies above `f`, does not create a hidden
positivity restriction on `n`.

## 6. Logical scope

The new arguments use finite Galois averaging (four radicals), ordinary
integer divisibility, finite recurrence identities, induction, and real
square-root inequalities. They are ordinary ZFC mathematics and work
internally in any model of ZFC; no claim about standard integers only,
bounded search, or experimental nonhalting is substituted for the proof.

The passage from the recovered source-system zero to a syntactic ZFC
refutation remains the parent package's inherited calibration theorem.
Accordingly this review establishes the new transformation relative to
that theorem. It does not turn finite code checks into an end-to-end
formal proof and does not independently certify global minimality or
novelty in the literature.

## 7. Finite-check receipt reviewed

The supplied circuit's literal weights agree with the stated roots:
`fa=16*delta*M^2*Dtau`, `fb=4*delta*M^2*Df`,
`fc=M^2*Dnum`, `fd=64*delta*(P1*mu^2)^2*Dmain`.
Its carrier centers are `V+2AI+4V0k`, and its main fractional numerator
has coefficient eight. The final circuit has 133 operations; its later
distribution of `W*Bt/(q-1)` into `L*Bt+Bt/(q-1)` preserves the displayed
polynomial exactly.

The exact-degree proof in `PROOF.md`, Section 3, was also independently
checked. Over the rational-function field in the direction variables,
the specified square roots have Laurent branches with the indicated
rational leading terms. Their errors from `Ct,Cf,V` have degrees
`1,0,-6`, while `d` has degree 2. The residual carrier's leading term
`-L_2*Bt_2` has degree 4. The sign classes therefore have respectively
8,4,2,2 factors of degrees 24,10,9,4. Their sum is 258, and the
prefactor contributes 448, proving exact degree 706. No cancellation
between these leading factors is possible because their product is a
nonzero element of the rational-function field. Independently expanding
the leading factors on the all-ones direction gives

```
9 * 2^202 * (2*beta)^366 * (2*beta-1)^8 * (2*beta-2)^2,
```

which is positive for the fixed coefficient. These algebraic conclusions
are not inferred from numerical root-search experiments.
