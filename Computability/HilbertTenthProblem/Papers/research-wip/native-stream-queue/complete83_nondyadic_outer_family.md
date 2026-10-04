# An actual-compiler even non-dyadic outer family

Fix any actual compiler produced by the original powers-of-five modified75 recipe, with its literal shared-projection83 fixed ports. There is an explicitly constructed infinite family satisfying all positive outer, repunit, packed-index, offset, and transport requirements with W=0 and even non-dyadic q. The ordinary input is constructed along with the family; it is not an arbitrarily prescribed input.

For each member, a single remaining finite arithmetic condition is sufficient for full positive completion: the exact four-term half-binomial divisibility test in Section6. This note does **not** prove that any member passes that condition, supplies no valid-program false-input example, and claims no universal83 bound. The fixed compiler constants are retained throughout; small diagnostic parameters in the companion are explicitly synthetic arithmetic checks, not substitute compiler programs.

All predecessor code is inert. The new helper uses only freshly written integer arithmetic and authenticates predecessor bytes without executing or importing their programs.

## 1. Exact fixed constants and a quantitative margin

Use

```
V=2^b, B=2^d=V^L, d=bL,
K=DC+B*DR,
MF_source=MF0+B−1.
```

Here b,L,d are the original positive powers of five, b>=5, and the actual layout has d>=25. K is the source's `Kconstant`, not the number of native positions. Retain the actual MC, MF0, DC, DR, all masks and all window coefficients. In particular

```
MC=2 mod4, 0<MC,MF0<B−1, MF_source<2(B−1).
```

The actual field exponent is Hfield=51M0+3a0+1, where a0 is the tile-alphabet size and M0>3a0. Complete76 chooses L>g_high+Emax, with Emax=27M0 and g_high=T2+Emax+1. Expanding the inherited definitions gives

```
L>213M0+4a0+4>4Hfield.
```

Thus DR=2^(b*Hfield)<B^(1/4), while DC<B by the actual coefficient/layout bound. Consequently

```
K+2<3 B^(5/4).                                   (1)
```

We will use the weaker margin K+2<4B^(5/4). For every integer d>=25,

```
64d < 2^(3d/4)=B^(3/4).                           (2)
```

For example the inequality holds at25, and its ratio increases with each integer increment of d. These inequalities will bound every constructed slack; no hypothetical asymptotic choice of an input-dependent compiler is being made.

## 2. Two fixed radix shapes cover every source coefficient K

Choose any positive n=1 modulo4 and put D=d*n and Q=B^n=2^D. D is odd and D=1 modulo4. Select one of the following shapes once according to the **fixed** residue of K:

| Shape | Condition | q | J | period factor T |
|---|---|---|---|---|
| plus | K !=3 mod5 | Q(Q+1)/2 | ((Q−1)/(B−1))*(Q/2+1) | n(D−1) |
| minus | K =3 mod5 | Q(2Q−1) | ((Q−1)/(B−1))*(2Q+1) | n(D+1) |

In both cases q−1=(B−1)J. The odd factors Q+1 and2Q−1 exceed1, so q is even and is not a power of two. Their exact two-adic exponents are D−1 and D, respectively. Both J are positive odd integers, and

```
q>=Q^2/2.
```

The powers-of-five assumptions are used only for this explicit residue construction. The separate compiler recipe at other odd primes is not silently included.

For a candidate positive integer z set

```
Z=C=z, F=K*z, W=0,
A0=q^2*(q^2−1)+(MC+q*MF_source)*J,
G0=(1+q*K)*(q^2−1),
R(z)=A0−G0*z.                                    (3)
```

This is exactly the source's packed index, not a new register or an alternative packing rule.

## 3. A small positive z makes the exponent congruence solvable

We choose z so that

```
1<=z<=4d, z=1 mod4, R(z)=b mod2d.                 (4)
```

First note B=2 modulo5, and n=1 modulo4 gives Q=2 modulo5 and (Q−1)/(B−1)=1 modulo5.

In the plus shape q=3 modulo5. Therefore

```
G0=(1+3K)*(3^2−1) !=0 mod5
```

precisely under its selected condition K!=3 modulo5. Since d is a power of five, G0 is a unit modulo d. Solve the single linear congruence

```
G0*z=A0−b mod d,
```

then combine it with z=1 modulo4. The least positive solution is at most4d.

In the minus shape q=1 modulo5 and J=0 modulo5. More precisely v5(J)=v5(q^2−1)=1. To see this, Q−1 and B−1 are units modulo5, whereas

```
2Q+1=2^(D+1)+1=4^((D+1)/2)+1.
```

The exponent (D+1)/2 is odd and prime to5 because D=1 modulo4 and5 divides D. The elementary odd-power binomial valuation gives v5(2Q+1)=1. Since q−1=(Q−1)(2Q+1), while q+1 is a5-adic unit, the asserted valuations follow. In the selected case K=3 modulo5, the factor1+qK is4 modulo5, so v5(G0)=1. Also5 divides A0 and b. Hence

```
(G0/5)*z=(A0−b)/5 mod(d/5)
```

has a solution because its coefficient is a unit. Combine with z=1 modulo4, obtaining 1<=z<=4d/5, which implies(4)'s bound.

In both cases A0 is even and G0 is odd. Thus odd z and odd b supply the missing congruence modulo2, yielding the full R(z)=b modulo2d. Since q is divisible by4 and J=1 modulo4, the literal packing also gives

```
R(z)=z+MC*J=z+2=3 mod4.                           (5)
```

This argument covers all residues of positive K. It does not require a new choice of the optional high monomial or any alteration of DC, DR, or the masks.

## 4. Positive input and raw slack

Let x be the unique integer in the interval[n,n+T−1] satisfying

```
x=(R(z)−b)/(2d) mod T.
```

The quotient is an integer by(4). Then

```
u=2dx+b, R(z)−u=0 mod(2d*T),
x>=n, x<=n(D+2), u>=2D+b.
```

Define the original supplied positive slack by

```
alpha=q−(K+2)z−2dx.                              (6)
```

Here C=q−F−Z−alpha−2dx=z exactly. Positivity follows uniformly, not just for sufficiently large n. From(1),(2) and z<=4d,

```
(K+2)z <16d B^(5/4)<B^2/4<=q/2.
```

Also 2dx<=2D(D+2)<=3D^2 for D>=25, and 3D^2<2^(2D)/8<=q/4. Thus alpha>q/4>0. In particular F,Z,C,alpha,x are strictly positive, F+2Z+2dx<q, and u<2q.

For completeness, the constructed packed index is in the required large positive range before any Pell completion. Formula(6) gives

```
q^2−Z−qF=q(2z+alpha+2dx)−z>3q.
```

Therefore R>3q+1 and R>u. Conversely the actual scalar mask bounds give

```
(MC+q*MF_source)J < (1+2q)(q−1).
```

Using F,Z>=1 in the exact packing then yields R<q^4−q^3, so R+2<q^4. Together with(5), r=(R−1)/2 is a positive odd integer well inside the accepted pretyping size domain.

## 5. Exact divisibility of X and the literal positive transport lift

Set X=2^R−2^u. This is positive because R>u. We prove the stronger divisibility q(q−1)|X.

In the plus shape, the odd factors of q(q−1) are

```
Q+1, Q−1, Q/2+1.
```

They are pairwise coprime: the first differs from twice the third by−1; the second and third have gcd dividing3, and Q=−1 modulo3 because D is odd. The other pair has gcd dividing2. Their multiplicative orders of2 divide2D, D, and2(D−1), respectively, so all divide

```
2D(D−1)=2d*T.
```

In the minus shape the odd factors are2Q−1, Q−1, and2Q+1. Again they are pairwise coprime; the only possible nontrivial cross gcd is3, excluded by Q=−1 modulo3. Their orders divide D+1, D, and2(D+1), all dividing2D(D+1)=2d*T.

Since R−u is a multiple of2d*T, the factor2^(R−u)−1 is divisible by every relevant odd factor, including all of its prime powers. The two-part of q is2^(D−1) or2^D, whereas u>=2D+b. Thus q(q−1) divides X as claimed. No primality assumption on Q+1 or2Q−1 is needed.

Put

```
w=X/q,
transport_quotient=1+z*w/(q−1).
```

Both are positive integers, and the source's transport factor is exactly

```
(K+w)C+q−F−transport_quotient*(q−1)=1.
```

Every outer quantity here uses the actual fixed compiler numerals. As n runs through1 modulo4, q increases without bound, so this is an infinite outer family. It does not hold the constructed ordinary input x fixed.

## 6. The remaining finite condition and conditional full completion

Define

```
r=(R−1)/2,
C_j=binom(2r,r+j),
M_r(X)=sum_(j=0)^r C_j*X^j,
Y=M_r(X)/2.
```

Y is a positive integer because X is even and the central coefficient is even. Exactly as in the accepted even-radix theorem, q is even and X is divisible by q, so

```
q^3 divides Y
iff C_0+C_1*X+C_2*X^2+C_3*X^3 =0 mod(2q^3).       (7)
```

This is the unresolved condition for the displayed outer family. The proof has not inferred it from repunit or transport compatibility. It can be tested without writing X explicitly, by modular exponentiation at modulus2q^3 and exact modular binomial arithmetic; that observation does not supply a uniform gate-cost improvement.

If a member satisfies(7), it admits the complete positive parametric extension of the shared83 offset/even-radix proof. The relevant hypotheses have been checked here: R=3 modulo4, 0<u<2q<R, X=2^R−2^u>2^(R−1), and Y is a positive multiple of q^3. Set s=Y/q^3 and use the first/main Pell definitions of those proofs. Their strict ratio sandwich gives positive eta,zeta and positive integral h. For the shared/input roots, W=0 gives U=E_u, and

```
sigma=((E_R−2^R)−(E_u−2^u))/H_Pell >0,
H_Pell=4a_Pell+3.
```

The odd index u gives the positive integral discriminant quotient. The general auxiliary completion m=2cR, f=chi_A(m), i=psi_A(m)/c^2, y_aux=psi_S(R), V=chi_S(R)/S and T=(V+c+Rf^2)/(cf) is positive and integral by the same multiple-index and two-congruence argument. Thus all seven normalized factors become+1 with exactly the source's18 positive witnesses. These are existential mathematical definitions, not new free circuit operations.

Such a completed member would be noncanonical because W=0 but2^u>0. It would still not, merely by being noncanonical, prove that its constructed input is rejected by the compiled machine. No passing member on an actual compiler is asserted here. The theorem establishes an exact reduction of this constructed family to(7), and preserves that final gap.

## 7. Evidence and nonduplication scope

The earlier positive-transport projection obstruction was read as context. It changes a supplied coordinate and uses negative F to evade the width bound; the present source and positive F remain unchanged, and R stays below q^4. The earlier non-dyadic q=76 diagnostic uses noncompiler constants; this theorem instead retains every actual compiler numeral but leaves(7) unresolved. Neither earlier mechanism is being relabeled as a new full zero.

The fresh helper pins the exact source/proofs, verifies the affine and modular construction on explicitly synthetic scalar cases, and records finite size-inequality and factor-period checks. These are corroborations of the all-compiler proof above, not evaluated universal programs, archived-source replays, materialized Pell zeros, or accepted/rejected language tests. The source remains unchanged; no new operation count or degree claim is made.
