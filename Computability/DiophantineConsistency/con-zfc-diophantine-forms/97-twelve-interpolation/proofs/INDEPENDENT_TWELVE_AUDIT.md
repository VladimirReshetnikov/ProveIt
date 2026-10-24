# Independent arithmetic audit of the twelve-integer construction

Audited object: `proofs/INTERPOLATION12.md`, with the corrected
auxiliary period `4 n0 f` and an even normalized strong coordinate `I`.
This audit concerns ordinary unbounded arithmetic, not a proof-assistant
certificate or an internally encoded derivation in the repository's ZFC
calculus. The native/compiler endpoint remains the explicitly inherited
source-34/source-71 endpoint.

The final selected main equation uses the homogeneous product weights in
Section 6 and has twelve integer variables and exact degree 4832. Earlier
common-weight bounds are retained below as intermediate derivations.

## 1. Verdict and two necessary corrections incorporated in the note

The new interpolation and signed soundness arguments pass this independent
audit. Two arithmetic corrections were necessary during development:

* A Pell period modulo `f^2` is `4 n0 f`; using `4 n0` alone is generally
  false. The corrected period does not change the CRT compatibility bound.
* Choosing `I` divisible by `4 s c^2` makes `I` even and `f` odd. Thus
  `gcd(f^2,4I^2)=1`, which justifies the interpolation quotient without a
  missing factor at the prime 2.

Neither is an additional equation or a restriction on soundness. Both are
choices of completeness witnesses. Arbitrary integer zeros are handled.

## 2. Normalized strong rank: no parity extension is needed

There is a useful simplification beyond the draft's restoration to the
ordinary strong kernel. The new square root of

    Df = 1 + Delta I^2,  I = s r c^2

already supplies a normalized integer Pell equation. Put
`B0=|a+2|>=2`, so `Delta=B0^2-1`. The main Pell equation supplies
`c0=|c|=psi_B0(p)`, with `p>=25` from the inherited first/main rank
bootstrap. Classifying the normalized strong equation gives

    |f|=chi_B0(m), |I|=psi_B0(m), m>=1.

Here `B0+sqrt(B0^2-1)` is the fundamental positive unit with integer
coefficients: any solution with positive second coordinate has first
coordinate at least `B0`, and the usual unit descent classifies all
solutions. Since `c0^2` divides `|I|`, strong divisibility gives `p|m`.
Write `m=p k` and put `C0=chi_B0(p)`. The binomial expansion gives

    psi_B0(pk)/c0 = k C0^(k-1) (mod c0).

The left side is divisible by `c0`, and `gcd(C0,c0)=1`; hence `c0|k`.
In particular `c0|m`, indeed `p c0|m`. Thus `m>=c0>2p`, exactly the
rank input needed by the inherited signed auxiliary step-down.

For that auxiliary argument set `rho=Delta I`. Then

    rho^2 = Delta(f^2-1),
    rho^2 = 1-B0^2 (mod |f|),
    rho^2 = 0 (mod c0).

The old exposed-quotient relations are restored by

    o=f(c-R+4IT),
    j_aux=Delta s^2 r^2 c^3(c-R)+4 s r c Df T,
    V=fo-c=c j_aux-R.

These are integer polynomial expressions. The auxiliary base `|rho|>1`
has odd Pell index because `chi_|rho|(2k)=(-1)^k (mod |rho|)`;
this statement requires no oddness of `rho` or its multiplier.

The signed proof now obtains `p=R`, `2n_first=R+1`, and
`X=sign(c) 2^R`. The fixed residue `X=2 (mod 3)` selects `c>0` and
`X=2^R`. Its first-index sign identity then gives `k>0`; the relation
`sign(c)=sign(k)sign(Y)` gives `Y>0`. Finally `q|2^R` and
`q=1 (mod beta)` exclude negative `q` by the Mersenne-radix lemma.
The post-power native decoder applies directly. One must not claim the
literal old coordinate `(Delta s r-1)/2` is an integer.

This direct normalized proof removes the need to generalize the imported
ordinary strong saturation lemma. It was independently pointed out by the
second auditor and checked here.

## 3. Elementary valuation bound used by interpolation

Let `I=psi_A(n)>0`, with integer `A>=2`. For every prime `p|I`,

    v_p(I) >= v_p(n).

For odd `p` dividing `Delta=A^2-1`, reduction of the Pell recurrence gives
`psi_A(k)=k A^(k-1) (mod p)`, so the first zero index is `p`.
For odd `p` not dividing `Delta`, the norm-one unit in the split algebra
or quadratic field over `F_p` has order dividing `p-1` or `p+1`.
Consequently the first zero index is prime to `p`.

If `p|psi_A(k)`, the binomial expansion of the `p`th power of
`chi_A(k)+psi_A(k)sqrt(Delta)` shows that the second-coordinate valuation
increases by exactly one: its first term has valuation
`1+v_p(psi_A(k))`, and every later term has larger valuation.
Multiplication of the index by an integer prime to `p` preserves that
valuation. These facts prove the asserted bound in both odd-prime cases.
For `p=2` and the even `A` used in completeness, the doubling identity
gives, for even `n`,

    v_2(psi_A(n))=v_2(n)+v_2(A).

Thus `gcd(n,I^2)|I`.

## 4. Correct period and full residue interpolation

Write `alpha=A+sqrt(Delta)` and `alpha^n=f+I sqrt(Delta)`. Reduction in
the integer-coefficient quadratic algebra modulo `f^2` gives

    alpha^(4n)=1-4f alpha^n (mod f^2),
    alpha^(4nf)=1 (mod f^2).

The second follows by the binomial theorem. Since `gcd(f,I)=1`, the
valuation bound proves

    gcd(4nf,4I^2) divides 4I.

For an arbitrary prescribed residue `a` modulo `I`, CRT therefore permits

    L=R (mod 4nf),
    L=R-4Ia (mod 4I^2).

Take `L>0`. Since canonical `R=3 (mod 4)`, this index is `3 (mod 4)`.
For `S0=Delta I`, put `V0=chi_S0(L)/S0`. The odd Chebyshev polynomials
`Q_m(X)=chi_s(2m+1)/s`, `X=s^2`, satisfy

    Q_0=1, Q_1=4X-3,
    Q_(m+1)=(4X-2)Q_m-Q_(m-1),
    Q_m(X)=(-1)^m(2m+1) (mod 4X),
    Q_m(1-A^2)=(-1)^m psi_A(2m+1).

These identities give simultaneously

    V0=-c (mod f^2),
    V0=-R+4Ia (mod 4I^2).

Canonical even `A` and odd `R` give `c=psi_A(R)=R (mod 4)` directly
from `psi_A(m+2)=-psi_A(m) (mod 4)`. Hence

    N0=V0+c-f^2(c-R)

is zero modulo `f^2` and is `4Ia` modulo `4I^2`. Because `f` is odd
and coprime to `I`,

    T=N0/(4If^2)

is an integer, and `T=a (mod I)` since `f^2=1 (mod I)`. Rearrangement
gives the required `V0=f^2(c-R+4IT)-c`. The Pell identity supplies the
auxiliary integer square root. The choice of `I,f` precedes the arbitrary
choice of residue `a`, so using intersectivity modulo this same `I` is
noncircular.

## 5. Safe smaller separator: degree 58 instead of degree 114

This is a drop-in improvement to the draft's common weight. Keep its
ordering of the four scaled radicals `Da,Dg,Dt,Df`. Write `ell=XY^2` and
define ordinary integer polynomials

    B_b = 1+c^2+R+c^2(s^2+r^2)(T^2+1),
    L = 8+B(Delta+c^2+3)+ell^2+k^2+Delta+I^2
          +Q(Df B_b+c^2+1)+3P+s^2,
    W = 2L+1.

The important logical order is unchanged. Before the strict guards have
been recovered, `W` is a nonzero integer because it is odd. This is all
that the lone-imaginary-root argument needs. After `P>0`, the determinant
guard gives `R>0`, so every summand in `L` is positive or nonnegative.

Here `R>0` does not use square extraction or any Pell rank theorem.
The determinant first gives common nonzero signs of `q,F,C,alpha`, where
`alpha=q-F-C`. For `q>0`, the factor
`q(q-F)-C=q alpha+(q-1)C` and the mask term `(MC+q MF)J` are both
positive. For `q=-Q<0`, write `C=-C0`, `alpha=-alpha0`. The first
factor is `Q(C0+alpha0)+C0>0`; also `J=-(Q+1)/beta<0` and
`MC-Q MF<0`, using the authentic bound `0<MC<beta<MF`.
Thus both summands in `R` are positive in either sign branch.

Set `b=c-R+4IT`. The elementary inequalities

    4|srT| <= (s^2+r^2)(T^2+1),
    |c| <= c^2+1

give `|b|<=B_b`, and therefore `|V|<=Df B_b+c^2+1`. At this stage
`Q>1`, `Da=(Q-1)(QV^2-1)>0`, and

    sqrt(Da) < Q|V| <= Q(Df B_b+c^2+1).

The other bounds are

    B sqrt(Dm)/|S| <= B(Delta+c^2+3),
    sqrt(Dt) <= 2+ell^2+k^2,
    sqrt(Df) <= Delta+I^2+3,
    sqrt(Dg) <= 3P+s^2+2.

For the first, use `|S|>=1`, `B>0` and
`sqrt(1+Delta c^2)<=1+(Delta+c^2)/2`. For the second, use
`sqrt(ell(ell+1))<=|ell|+1` and two applications of `2|xy|<=x^2+y^2`.
The third is the same inequality as the first. For the fourth use
`Dg<=3P s^2+1` and `2 sqrt(3P)|s|<=3P+s^2`.

Thus the displayed `L` exceeds the sum of all five unweighted radical
magnitudes. The original superincreasing-weight proof works verbatim.
The maximal degree of `L` is exactly 58: `Q` has degree 32, `Df` degree
20, and `B_b` degree 6. The last radicand has degree

    deg(S^2 W^8 Df)=68+8*58+20=552,

strictly greater than the other four. The norm therefore has exact
degree `16*552=8832`, once the new circuit's leading form is checked.
The leading degree-58 part of `L` is

    a0^6 I0^4 c^2(s^2+r^2)T^2,

where `a0` and `I0` are the leading forms of `a` and `I`. It is nonzero,
so the degree claim does not depend on cancellation among coefficient
ports. This change adds no variable and alters no completeness step.

## 6. Product weights and the final degree-4832 separator

The same four individual bounds give a further reduction without changing
any arithmetic coordinate or interpolation argument. Define

    M0 = B(Delta+c^2+3),
    Ma = Q(Df B_b+c^2+1),
    Mf = Delta+I^2+3,
    Mt = 2+ell^2+k^2,

and the four ordinary integer polynomial weights

    wa = 2M0+1,
    wf = wa(2Ma+1),
    wt = wf(2Mf+1),
    wg = wt(2Mt+1).

Every weight is odd on every integer assignment and therefore nonzero.
Thus all early nonzero and single-imaginary-root arguments remain valid
before the guards. After the guards, all four bounds and weights are
positive. Replace the five norm radicands by

    A0 = B^2 Dm,
    A1 = S^2 wa^2 Da,
    A2 = S^2 wf^2 Df,
    A3 = S^2 wt^2 Dt,
    A4 = S^2 wg^2 Dg.

The center remains `Sn-A`.

### Separation proof

After division of a vanishing conjugate factor by `S`, the five radical
magnitudes, in this order, are

    x0=B sqrt(Dm)/|S|,
    xa=wa sqrt(Da),
    xf=wf sqrt(Df),
    xt=wt sqrt(Dt),
    xg=wg sqrt(Dg).

The previously proved bounds give

    x0<=M0<wa/2,
    x0+xa < wa(1/2+Ma)=wf/2,
    x0+xa+xf < wf(1/2+Mf)=wt/2,
    x0+xa+xf+xt < wt(1/2+Mt)=wg/2.

Each nonzero integer radicand has square root at least one. Therefore
each new nonzero magnitude strictly exceeds twice the sum of all earlier
magnitudes. If `Dg=0`, delete its zero contribution. This proves the
same square-class separation required by the draft: a rational linear
combination of the radicals cannot have a nonzero contribution from a
nontrivial rational square class, since that class's largest term cannot
be canceled by its smaller terms. Every base square root is rational,
and consequently integral.

For completeness the final coordinate is now

    n=(A+B d)/S+wa ytilde+wf f+wt tau+wg g.

All weights depend only on already chosen coordinates, so the witness
order and its absence of circularity are unchanged.

### Degree audit

The degrees of `M0,Ma,Mf,Mt` are respectively `40,58,12,20`.
Their leading forms are nonzero. Consequently

    deg(wa)=40, deg(wf)=98, deg(wt)=110, deg(wg)=130.

The five radicand degrees are respectively

    70, 262, 284, 322, 374.

The center has degree 35. The last radicand is uniquely largest. In the
32-factor norm, taking that radical in every factor gives `A4^16` with
coefficient 1; all other terms have lower total degree. Thus the total
degree is exactly `16*374=5984`.

An explicit noncancellation certificate follows. Write the leading forms

    q0=6 beta j, W00=12w, Y0=2v q0^3,
    a0=q0 W00 Y0=2^7 3^5 beta^4 j^4 w v,
    I0=s r c^2,
    P4=5(4T-c)^4+10(4T-c)^2 c^2+c^4.

Then

    lead(M0)=a0^6 P4,
    lead(Ma)=a0^6 I0^4 c^2(s^2+r^2)T^2,
    lead(Mf)=a0^2,
    lead(Mt)=(a0 Y0)^2,
    lead(S)=2^10 I0 a0^5,
    lead(Dg)=-3s^2 Y0^4 h^4 a0^4.

Therefore the leading part of the last radicand is

    -3*2^28 I0^10 a0^46 P4^2 c^4(s^2+r^2)^2 T^4 s^2 Y0^8 h^4.

Its sixteenth power has a nonzero coefficient at the monomial

    j^3328 w^736 v^864 h^64 T^192 s^256 r^160 c^384,

namely

    2^6368 3^4080 5^32 beta^3328 > 0.

The monomial exponents sum to 5984. The maximal `T` power selects the
`5(4T)^4` term in every `P4`; the stated `s,r` exponents select `s^2`
in every remaining `(s^2+r^2)` factor. Thus no other term can cancel
this coefficient. This certificate uses only the already explicit fixed
integer `beta`.

### Final homogeneous improvement: replace only the first bound

The final selected polynomial improves the preceding coarse `M0` by using
the homogeneous structure of the quintic. Set

    K=T^2+c^2+1,
    M0_new=256K^2,
    wa=2M0_new+1=512K^2+1,

and keep the same definitions of `wf,wt,wg` in terms of `Ma,Mf,Mt`.
This is the degree-4832 polynomial. The preceding degree-5984 derivation
records the intermediate bound only.

Here is the complete proof of the new bound. After `S!=0`, one has
`c!=0`, `|I|>=c^2`, and therefore `|c|>=1`. The front definitions imply
`|a|>3`, `|X|<|H|`, and

    |a|/|H|<1/3,  2|a+2|<|H|.

Indeed `H=4a+3`, while `|a|=|X+1||Y|` with `|X|>=64` and
`|Y|>=4096`. Recall that the source's `b0=X+ac`, and put

    y=u/H=T-b0/H,
    z=sqrt(Dm)/|H|.

Then

    |b0/H|<1+|c|/3,
    |y|<|T|+1+|c|/3,
    y^2<=3(T^2+1+c^2/9)<=3K.

Since `c^2>=1`, the identity `Dm=1+Delta c^2` gives
`sqrt(Dm)<=|a+2||c|`. Consequently `z<|c|/2` and in particular
`z^2<=K`. The exact quintic coefficient identity is

    B/H^4 = 5y^4+10y^2 z^2+z^4
              +32(3y^2+z^2)+2y+31.

Using `2|y|<=y^2+1`, this is bounded above by

    76K^2+323K+32 <= 431K^2.

Finally

    B sqrt(Dm)/|S|
      = (B/H^4) z/|I|
      < 431K^2 |c|/(2|I|)
      <= (431/2)K^2
      < 256K^2=M0_new.

No guard sign, square extraction, or Pell rank theorem is needed for this
bound beyond the already established `S!=0`. The product-weight separation
proof above is otherwise unchanged.

The final weight degrees are `4,62,74,94`; the five radicand degrees are

    70, 190, 212, 250, 302.

Hence the final norm has exact degree `16*302=4832`. Its last-radicand
leading form is

    -3*2^44 (T^2+c^2)^4 a0^34 I0^10 c^4(s^2+r^2)^2
        T^4 s^2 Y0^8 h^4.

The sixteenth power has the explicitly positive coefficient

    2^5024 3^3120 beta^2560

at

    j^2560 w^544 v^672 h^64 s^256 r^160 c^384 T^192.

These exponents sum to 4832. The maximal `T` and stated `s,r` powers
again give unique selections in the displayed leading product. The
coefficient and degree have been independently corroborated against the
construction author's calculation. No additional candidate improvement
is proposed in this audit.

## 7. Audited inherited references

The repository snapshot inspected by the parent is
`04a1d79222d55cabe4ba52897863fc33baa8c268`.

* `docs/incoming/ZFC_Diophantine_Joint_Guards_2026-10-24.zip`, internal
  `ZFC_Diophantine_Joint_Guards/guards/PROOF.md`, Section 4:
  signed first/main rank bootstrap, auxiliary step-down, and delayed
  residue orientation.
* The same archive, internal `guards/upstream/residue/PROOF.md`,
  Sections 4.1--4.6: explicit signed rank and ratio arguments.
* `docs/incoming/ConZFC_13_Integer_Norms_2026-10-24.zip`, internal
  `con-zfc-root-fusion-2026-10-24/provenance/PROOF44.md`, Sections 6--7:
  Mersenne sign exclusion and direct post-power native decoding.
* The same archive, internal
  `provenance/upstream_ordinary/source25_ordinary_blank.md`:
  ordinary signed auxiliary and blank compiler interfaces.

Pinned archive URLs are formed by inserting the displayed commit after
`https://github.com/VladimirReshetnikov/ProveIt/blob/` and appending the
listed `docs/incoming/...zip` path. The files copied into the final packet
must preserve their upstream notices and exact coefficient bindings.

### Status of the inherited endpoint

The supplied native/compiler and K215-calibration documents present
completed ordinary proofs; they are not conjectural interfaces or
undischarged mathematical assumptions. For example,
`provenance/upstream_ordinary/k215_ordinary.md` explicitly records the
quantified primitive runtime theorem, calibrated blank startup, and
dominated-calculus equivalence, and concludes the ordinary ZFC-provable
equivalence between blank halting of the exact K215 table and existence
of a finite ZFC refutation. The source-34 coefficient adapter presents
the complete decoder and canonical completeness argument for its exact
tuple. This audit uses those supplied proofs as inherited lemmas and
checks the new construction's interface to them; it does not independently
repeat every machine/runtime/compiler proof.

Accordingly, the proposed ordinary mathematical theorem is a ZFC-provable
equivalence, by composition of those proved lemmas with the new arithmetic
proof. The separate limitation is proof-assistant and object-calculus
coverage of the final polynomial theorem. An executable finite circuit
check must not be described as a formal verification of this entire
unbounded mathematical proof. No proof of Con(ZFC), or assumption that
ZFC is consistent, is used in constructing the coefficients or proving
the equivalence.
