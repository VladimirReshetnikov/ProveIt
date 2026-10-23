# Independent proof audit: fourteen positive variables, degree 26

Audited object: `carrier14.py`, with `shift_x=True`. Both transport choices
are covered; the shifted transport has 92 live arithmetic gates and the
unshifted transport has 93. The audit is against the repository snapshot
`beb0192cb8dc36f78c369c080f2adfbc1887a486` and the complete ordinary
strong-rank argument preserved in package 36 / source 31.

**Conclusion:** the simultaneous carrier is sound and complete under the
stated compact native compiler interface. The bootstrap does not assume
`q | X`, `p=R`, or a restored old index coordinate. The shift `X=x+q`
must be retained for this proof. Its completeness is justified by the
canonical identity `X=2^R`, which gives `w=X/q>q>1`.

## 1. Formula under review

All fourteen supplied coordinates

    j,F,alpha,z,f,i,T,x,Y,r,eta,zeta,u,gamma

are strictly positive. Write

    J=3j+1, q=beta J+1, X=x+q,
    C=q-F-alpha, E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, A=a+2, H=4a+3, Delta=A^2-1,
    ell=EkY, K=4qY, M=qK=4q^2Y, idx=k-R-1,
    b0=X+ac,
    Dstar=M b0+H(M gamma-idx+KX),
    Nm=Dstar^2-M^2(1+Delta c^2),
    A0=[q^3(ell+r)+Y]^2-q^6[ell(ell+k)+1],
    U=Delta(f^2-1), I=ic^2,
    V=f^2(cT-R)-c,
    Aa=(V+u)^2-Uu(2V+u)-1,
    As=I^2-U.

Here `R` and the fixed ports are exactly the compact native expressions.
The unshifted transport residual is

    At=q[K0 C+(q-F)-z(q-1)]+XC-q;

the shifted residual is

    At=(qK0+X)C-qF-qz(q-1).

The final polynomial is `A0^2+Nm^2+At^2+Aa^2+As^2`.

## 2. Initial bounds do not use recovered coordinates

The first residual gives `q^3 | Y` by the integrality of rational square
roots of integers. Set `s=Y/q^3` and `tau=ell+r+s`; both are positive,
and `tau^2=ell(ell+k)+1`.

The supplied congruence gives `q=2 mod 3`, because the actual compact
port is `beta=2^590069-1=1 mod 3`. Since `q | Y`,

    H=4Y(X+1)+3=3 mod q,
    gcd(q,H)=1.

Both transport forms give `C>0` before `q | X` is known. For the shifted
form this follows directly from its positive right side. For the
unshifted form, divide by positive `q` only as a rational equality:

    (K0+X/q)C+(q-F)-z(q-1)=1.

If `C<=0`, the left side is at most `1-F<=0`. Thus the native mask bounds
apply and give

    q>=16, 3q<R<q^4-2, E>=q^4>R+2.

The last inequality uses the supplied shift `X=x+q>q` and `Y>=q^3`.
It does not use the desired conclusion `X=wq`.

## 3. Main integrality and the first, deliberately weaker modulus

The main residual gives `M | Dstar`. Moreover `Dstar>0`. Indeed
`idx<k`, `b0>akY`, and `H<5a`, so

    Dstar > M b0-Hk > ak(MY-5)>0.

Consequently `g=Dstar/M` is a positive integer satisfying
`g^2-Delta c^2=1`, and

    M | H(idx-KX).

Reduce this only modulo `K`, obtaining `K | H idx`. Since `H` is odd,
`gcd(q,H)=1`, and `gcd(Y,H)=gcd(Y,3)`,

    d=gcd(K,H)<=3,
    mu=K/d >= 4qY/3 >= 4q^4/3 > R+1.

Thus `mu | idx`. No division by `q` inside `X` has been made.

## 4. Bootstrap before rank recovery

Positive Pell classification gives

    P0=2EY+1,
    tau=chi_P0(n), k=2 psi_P0(n),
    g=chi_A(p), c=psi_A(p), n,p>=1.

Here `P0>A` and `c>k`, hence `p>n`. Also

    k=2n mod 4EY.

Because `q | Y`, one has `K=4qY | 4XY^2=4EY`, and hence

    2n=R+1 mod mu.

The bounds `0<R+1<mu` and `n>0` imply

    2n=R+1+t mu with t>=0,
    n>=(R+1)/2>=25, p>=26.

Therefore

    c>A Delta^2, c>2p, c>2R.

For example `c>=A^(p-1)>=A^25>A^5>A Delta^2`, and
`c>=psi_A(2)=2A>2R`.

## 5. Ordinary strong-rank and auxiliary recovery are applicable

The equation `As=0` gives `I^2=Delta(f^2-1)` with `I=ic^2>1` and
`f>=2`. The ordinary strong-rank lemma is a statement about
`A,Delta,c,p,I,f`; it does not require that the outer coordinate `w`
or the deleted index coordinate has already been restored. Its only
large-rank hypothesis here is precisely `c>A Delta^2`, now established.

It yields an integer `m` with

    f=chi_A(m), p|m, c|m, m>=c>2p,
    I=Delta psi_A(m), c^2 | f^2-1.

The auxiliary residual is exactly

    I^2 V^2-(I^2-1)(V+u)^2=1.

Its ordinate `y=|V+u|` is nonzero: otherwise `I^2 V^2=1`, impossible
for `I>1`. Both necessary congruences hold:

    V=-c mod f,
    V=-R mod c.

The second uses the now-proved divisibility `c^2 | f^2-1`. The signed
auxiliary-index proof from ordinary source Sections 4--5 gives `p=R`.
It is essential to use that signed proof; positivity of `V` is neither
assumed nor needed.

## 6. Recover the full modulus and then X/q

As `p>n` and `p=R`, one has `1<=n<R`. Thus

    |2n-R-1|<R<mu.

Combined with the congruence modulo `mu`, this gives `2n=R+1`.
Consequently `idx=k-2n` is a positive multiple of `4EY`. The positivity
follows from `n>=25` and `psi_P0(n)>n`.

Now `M | 4EY`: the quotient is `XY/q^2`, an integer because `q^3 | Y`.
Thus `M | idx`. Returning to the original main divisibility gives

    M | HKX,
    q | HX,
    q | X.

The final implication uses `gcd(q,H)=1`. Set

    w=X/q,
    h=idx/E,
    gamma_old=gamma-idx/M+w.

These are integers; `w,h>0`. The main carrier becomes

    g=X+ac+H gamma_old.

Also `n>=2` gives `k>=4P0>X`, so `c>X`; since
`g>(a+1)c`, one obtains `gamma_old>(c-X)/H>0`.

Take `T_old=fT`, `y=|V+u|`, and take `z_old=z` for the unshifted
transport or `z_old=z+1` for the shifted transport. All ordinary
coordinates are positive, and all six ordinary factors equal `+1`.
The inherited compiler soundness theorem is therefore applicable.

## 7. Completeness and positive offsets

Canonical compact witnesses have

    q=B^N, J=1+B+...+B^(N-1),
    B=2^590069, N=581197^e>1 odd,
    X=2^R=wq, Y=sq^3,
    p=R=2n-1, R=3 mod 4, n>=3.

Therefore `j=(J-1)/3>0`, `w>q`, and `x=X-q>0`.
For the shifted transport, the standard argument `w>q>F` gives
`z_old>=2`, so `z=z_old-1>0`.

Keep `Y` directly and set `r=tau-ell-s`. The first-root estimate
`tau-ell>k/3>XY/3>s` gives `r>0`.

The canonical index identity makes `idx=k-2n` a positive multiple of
`4EY`. Hence `M | idx`. Define

    gamma=gamma_old+idx/M-w.

There is a particularly short local positivity proof: since the positive
multiple is at least `4EY`,

    idx/M >= XY/q^2 = wY/q >= wq^2 > w.

Thus `gamma>0` follows already from `gamma_old>0`; package 58's stronger
main-root gap `gamma_old>w` is available but unnecessary here. Substitution
gives `Dstar=M g`.

Use package 58's squared-modulus auxiliary construction, which is
coefficient independent after the canonical conditions above:

    V*=chi_I(R)/I, y*=psi_I(R),
    T=(V*+c+Rf^2)/(cf^2), u=y*-V*.

The odd-polynomial identities and `R=3 mod 4` give
`V*=-c mod f^2` and `V*=-R mod c`; `gcd(c,f^2)=1` makes `T` integral.
Both `T` and `u` are positive. The ordinary strong coordinate is the
usual `i=Delta i_normalized` when starting from normalized witnesses.
All five new residuals vanish.

## 8. Exact degree check

Let `q0=3 beta j`, `X0=x+q0`, `k=eta+zeta`, and

    R0=q0^3(q0-F), M0=4q0^2Y.

The residual degrees are respectively

    deg(A0,Nm,At,Aa,As)=(11,13,3,13,10).

For the main residual write

    Z=MX+H(M gamma-idx+KX), Dstar=Mac+Z.

Then the exact cancellation identity is

    Nm=2MacZ+Z^2-M^2 Hc^2-M^2.

Its leading form is

    Lm=32 q0^2 X0^2 k Y^4 (4q0^2 Y gamma+R0).

The auxiliary leading form is

    La=2 X0^2 Y^2 f^4 u R0.

Hence the degree-26 leading form of the final polynomial is
`Lm^2+La^2`, which is nonzero. In particular the coefficient of
`x^4 Y^4 f^8 u^2 j^6 F^2` is `4(3 beta)^6>0`, and `Lm^2` has no `u`
with which to cancel it.

## Scope of the audit

This establishes the new reduction from the stated ordinary compact
compiler interface. It is an ordinary mathematical proof, not a Lean/Rocq
end-to-end verification of the compiler or K215/refutation calibration.
The actual coefficient tuple and upstream compiler proof remain required
dependencies; arbitrary fixed-port substitutions do not inherit the
consistency interpretation.
