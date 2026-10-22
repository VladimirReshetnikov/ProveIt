# A 27-integer equation obtained by signed root amalgamation

This is an ordinary mathematical reduction of the pinned constructions, not
a new Lean/Rocq verification. All sources are at
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035` in
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
Use the coherent four coefficient ports of `14-integer29` (the inherited
`06-blank67` tuple), including its shifted MF. The validity of its native
compiler and K215 endpoint is inherited, not independently re-proved here.

The final package instead binds its default to the coherent reduced T4
tuple in `INSTANCE.json`. Section 6 of `compiler/PRUNED_T4_PROOF.md`
verifies transfer of the positive mask bounds and canonical odd-i,
square-w choices, using odd `d0=5^16`, power-of-five padding and
`R=3 mod 4` tuning. The proof below therefore applies to that whole tuple
as well as the original fallback. No coefficient ports may be spliced.

## 1. Formula before the positivity surjections

Keep seven positive coordinates

`J,F,alpha,z,s,eta,zeta`.

Let `h,T,gamma,r,u,v0` be unrestricted integers, and put

`i=2r+1, w=u^2, t=2v0+1`.

Thus there are thirteen coordinates in this mixed domain. Use these
abbreviations (all are substituted polynomials, not additional variables):

```
q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3, Delta=a^2+H,
Dmain=X+ac+gamma H,
R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
Nmain=Dmain^2-Delta c^2,
Nindex=k-hE-R,
Ntransport=(K+w)Cw+q-F-z(q-1),
A=1+(EkY)(EkY+k),
Q=(Delta i c^2)^2,
D=1+Delta i^2 c^4,
v=cT, Z=c+RD, d=Q-1,
e=Q(Dv^2+Z^2)-1,
M=2(D+v^2),
C=d(t^2+M^2 A)-e,
B=2QvZ,
U=C^2+DB^2-4d^2 t^2 M^2 A,
Res=U^2-D(2CB)^2.
```

The equation is

`Nmain Nindex Ntransport (1+Res)-1=0`.

For each of the seven positive coordinates substitute an independent copy
of `Pos(x,y,z)=x^2+x+y^2+z^2+1`. This yields exactly
`7*3+6=27` unrestricted integer coordinates.

## 2. Unit signs and the zero power scale

At a polynomial zero, the four factors are integer units. Since
`Delta=(a+2)^2-1` is 0 or 3 modulo 4, `Nmain` cannot be -1. Also `Res` is a
square modulo 4, so `1+Res` cannot be -1. Consequently

`Nmain=1, Res=0, Nindex=Ntransport=epsilon in {+1,-1}`.

Initially `w>=0`, while `Y,k,c,a,H,Delta` are positive. If `w=0`, then
`X=0`, `a=Y`, and `Dmain=ac+gamma H`. Reducing the main norm modulo H gives
`0=1 (mod H)`, impossible because `H>1`. Hence `w>0` and `X>=q`.

The weak transport bootstrap from `14-integer29` now gives `Cw>=0`,
`q>=16`, `0<R<q^4-2`, and `E>=q^4>R+2`. Because `h` is integral,
`k=R+epsilon+hE>0` forces `h>=0`. Therefore `k>=R-1`, so `R<=k+1<=2k`.
Also `Y>=q^3>=4096` and `c<k(Y+1)`.

## 3. The denominator C is positive even with signed T and h

Write `U0=XY^2`. Then

`A=1+k^2 U0(U0+1)>k^2 Y^4`.

For `Y>=4`, `Y^4>8((Y+1)^2+4)`. Combined with the bounds just proved,
this implies `A>8(c^2+R^2)`. Since `D>1`,

`(D+v^2)^2>=4Dv^2`,
`(D+v^2)^2>=D^2`,
`Z^2=(c+RD)^2<=2D^2(c^2+R^2)`.

Splitting `AM^2` into halves, these inequalities imply

`AM^2>2(Dv^2+Z^2)`.

Since `Q>=2` and `d=Q-1>=Q/2`, we get

`dAM^2>Q(Dv^2+Z^2)=e+1`.

Thus `C>0`. Notice that this proof allows arbitrary signs of T and t;
the only property of t needed later is `t!=0`, guaranteed by its odd form.

## 4. The exceptional T=0 branch is impossible

The other denominator `B=2QvZ` vanishes exactly when `T=0`. Suppose this
occurs. Then `v=B=0`, `Res=U^2=0`, and

`C^2=4d^2 t^2 M^2 A`.

The rational number `tau=C/(2dtM)` has integer square A, hence is an
integer. Then `y=t-M tau` is an integer and direct expansion gives

`d y^2=e=Q Z^2-1`.

But `1<Z<Q`. The lower bound is immediate. For the upper bound, use
`Q=Delta(D-1)`, `Delta>R`, and `D>=1+Delta c^4` to obtain

`Q-Z=(Delta-R)D-Delta-c >= D-Delta-c >0`.

Here `c>=2`. The restored auxiliary equation would therefore imply

`y^2-Z^2=(Z^2-1)/(Q-1)>0`.

As y,Z are integers, its left side is at least `2Z+1`. Its right side is
strictly less than Z because `Z<=Q-1`. Contradiction. Hence `T!=0` and
`B!=0` at every solution.

## 5. Recovering f, tau and y

Now all proof-only denominators in

`f=-U/(2CB)`,
`tau=(C+Bf)/(2dtM)`,
`y=t-M tau`

are nonzero. The equation `Res=0` gives `f^2=D`, so f is an integer.
The identity `U+2CBf=0` then gives

`(C+Bf)^2=4d^2 t^2 M^2 A`.

Thus `tau^2=A`, and tau is an integer. Therefore y is also an integer.
Expanding the definitions gives

`d y^2=e-Bf=Q(vf-Z)^2-1`.

Since `f^2=D`, the integer `V=vf-Z` is exactly
`c(Tf-1)-Rf^2`. We have restored all three eliminated equations:

`tau^2-(EkY)(EkY+k)=1`,
`f^2-Delta i^2 c^4=1`,
`Q V^2-(Q-1)y^2=1`.

No sign claim is made about the restored roots. None is zero: A,D>1 and
`Q V^2=1` is impossible. These, the main norm, and the two equal unit signs
are precisely the expanded signed-domain hypotheses proved sufficient in
`14-integer29/proofs/signed_domain_proof.md`. That proof accepts arbitrary
integer h,T,gamma,f,tau,y, odd i and square w. It forces both remaining
unit signs positive, recovers the packed blank K215 computation, and hence
a finite ZFC refutation. This establishes soundness.

## 6. Completeness and the new odd t condition

Start with the canonical witness selected in the completeness proof of
`14-integer29/proofs/signed_domain_proof.md`. It supplies i odd and w a
square, with canonical final rank R odd, c odd, and Aparam=a+2 even.
For its selected strong index `m=cR`, the number `psi_Aparam(m)` is odd;
thus `rho=Delta psi_Aparam(m)` is odd. The canonical auxiliary root
`y=psi_rho(R)` is odd, since rho and R are odd (this also follows directly
by reducing the Pell recurrence modulo 2).

Set `M=2(D+v^2)` and `t=M tau+y`. M is even, so t is odd. It is positive
in the canonical positive tuple, and can therefore be written `2v0+1`.
Substitution into the three square relations gives
`C+Bf=2dtM tau`, `U+2CBf=0`, and hence `Res=0`. All four product factors
are then 1. Thus any blank K215 halting computation gives a solution of
the proposed equation.

The positive surjection Pos represents every positive integer: apply the
three-square theorem to `4n-3`, whose representation has one odd square
and two even squares. Consequently it preserves this existence statement.
The resulting 27-integer equation is solvable exactly when K215 halts,
and its lack of solutions is equivalent to Con(ZFC) by the inherited
machine calibration. All steps are ordinary mathematics formalizable in
ZFC; this does not prove Con(ZFC).

## 7. Size and independent algebra checks

`integer27_product139.json` is a full straight-line evaluator with 27
unrestricted integer inputs, 139 binary operations (74 multiplications,
65 additions/subtractions), and degree 1116. Every gate and input is live.
The count is 84 inherited gates, one even-weight gate, five affine/square
substitution gates, and 49 gates for seven Pos substitutions.

The degree is exact uniformly for the positive compiler coefficients.
After substitution, q,Y,X,E,k,c,a,Delta,R have degrees
`2,8,4,12,2,10,12,24,8`, respectively. The main norm's degree-44 terms
cancel, leaving degree 35 with its nonzero top contribution `2ac gamma H`.
The index and transport have degrees 13 and 4. Further,

| Register | A | Q | D | v | Z | M | e | C | U | Res |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Degree |44|90|66|11|74|66|238|266|532|1064|

C has the unique top degree contribution `d M^2 A`; U has the unique
top contribution C squared; Res has the unique top contribution U squared.
The product degree is therefore `35+13+4+1064=1116`. The four-equation
system has maximum degree 1064 and can use the same 27 variables.

`build_integer27.py` independently evaluates the displayed formula against
the emitted DAG on 100 signed assignments and performs two modular
univariate degree specializations. These are algebra checks, not a test of
the full (astronomical) coefficients or an accepting K215 witness. Its
results are in `integer27_checks.json`. No global optimum or new universal
Diophantine bound is claimed.
