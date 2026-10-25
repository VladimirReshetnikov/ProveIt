# Independent review of the full-modulus Pell rebasing

Reviewer: a separate AI-assisted mathematical audit task, 25 October 2026.
Comparison snapshot: ProveIt commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`.

## Accepted conclusion and its scope

The four equations in `signed/` pass this review of the
new mathematical reduction and of the changed algebraic formulas:

| Equation | Unrestricted integer unknowns | Exact degree | Live binary operations |
|---|---:|---:|---:|
| `integer14_degree82.json` | 14 | 82 | 113 |
| `integer14_degree90.json` | 14 | 90 | 111 |
| `integer13_degree152.json` | 13 | 152 | 126 |
| `integer11_degree298.json` | 11 | 298 | 150 |

The corresponding comparison points are 14/86/112, 14/94/110,
13/156/125 and 11/300/148. Each new point lowers degree at a small
operation-count cost. This is not a global minimum theorem. The six fixed
coefficient integers and their source calibration are inherited; this work
does not reduce their height or replace their underlying refutation compiler.

The accepted mathematical conclusion is conditional on the precisely retained
ordinary source theorems: authentic mask bounds, signed Pell classification
and rank, auxiliary step-down, ratio and projection lemmas, supported-modulus
interpolation, the intersective quintic, and the native/compiler/refutation
calibration. The review checks that the new hypotheses needed by these
theorems are established before use and that an actual calibrated source zero
is restored. It does not certify the entire inherited chain in a proof
assistant or prove Con(ZFC).

The particularly important restoration detail is that the new magnitude
guard does **not** imply the old one. Soundness must restore a source whose
guard is only B0>0, with fresh positivity witnesses. It must also replace
the old h-coordinate by `h_old=Y*h_new`. These two details are substantive,
not matters of notation.

## 1. The changed common kernel

Use the notation of the component's `PROOF.md`. The changes are

    ell=XY^2,
    k=R+1+h ell,
    Budget6=Y^2 B0-k^2 q^6,

where the previous front used `k=R+1+hXY` and subtracted `k^2 q^8`.
The first Pell norm is still

    1+ell(ell+1)k^2.

Thus its recurrence already supplies a congruence at the larger modulus ell.
No new recurrence, root witness or unknown is needed to use that modulus.

At a zero, the ternary positivity condition gives Budget6>0. This excludes
k=0 and Y=0 and implies B0>0. Since B0<=k^2 q^2, it gives

    |Y|>|q|^2.

The centered disk consequences of B0>0 are unchanged, including
`|c/k-Y|<1/2`, c nonzero, and the common strict sign of q,F,C,q-F-C.
The authentic mask bound therefore gives, with q0=|q|,

    q0(q0^2-1)<R<q0^4-2.

The affine restrictions give q0>=16, |X|>=4q0, X divisible by8 and
X=2 modulo3. Hence

    |ell|=|X|Y^2>4q0^5>3R+1.

This argument does not use a power-of-two projection or the eventual cubic
scale. It establishes exactly the no-wrap magnitude that is needed next.

## 2. Sound order of the common Pell bootstrap

The carrier is a monic quadratic in the rational number Z/U. Here U is
nonzero unconditionally, because q is nonzero and H is odd. The rational
root theorem makes Z/U integral. Its parity then supplies the integral root
of `1+ell(ell+1)k^2`. Moreover U|Z yields

    M|H(Y-q^3),  H|M Klo.

The first relation forces Y even using only the 2-primary part and odd H.
It does not yet justify cancelling H modulo M.

Let B=|A|, P=|2ell+1|. The retained folding/classification gives

    |c|=psi_B(p),  |k|=2psi_P(n0),  p,n0>=1.

The conditions |X|>=64 and |Y|>256 ensure P>B. The centered strip gives
|c|>|k|. Monotonicity in index and Pell parameter therefore gives p>n0.
The elementary recurrence congruence

    psi_(2ell+1)(n)=n modulo 2ell

is valid for every natural n and every nonzero integer ell. Correcting for
the sign of the Pell parameter gives

    epsilon 2n0=R+1 modulo |ell|,
    epsilon=sign(k) sign(X)^(n0-1).

If epsilon=1, positivity and the new modulus bound imply
`n0>=(R+1)/2`. If epsilon=-1, then `2n0+R+1` is a positive multiple of
|ell|, so it exceeds 3R+1 and n0>R. These are the same two index bounds
used by the retained rank proof. They do not require |XY| to be large.

At this point the large-ordinate conditions for strong rank and auxiliary
step-down follow from Pell growth. Their literal divisibility and residue
hypotheses are unchanged. They give p=R. The negative branch would now
contradict p>n0, and the positive branch has no wrapping. Consequently

    2n0=R+1,  R=2t+1,  t>=24.

The retained sign-uniform ratio estimate requires only |X|>=64, |Y|>=6,
these exact indices, the same two Pell parameters, and the centered interval.
All of those hypotheses have now been proved. It yields

    |Y|>(|X|-3)^t/2-1,
    |H|>|X|(|X|-3)^t.

The previous larger guard supplied much more scale magnitude than this
stage actually needed.

## 3. Projection and the correct predecessor map

The early carrier gives `H|q^3 Kq` via

    2Kq-Klo=HXc,  Kq=X(X+2ac)-1.

The signed Pell projector turns this into divisibility of the whole product

    q^3(sign(c)X-2^R)(2^R sign(c)X+1).

For x=|X|>=64 and t>=24, `(x/32)^t>=x^4`. The preceding ratio bound
therefore gives |H|>16^t x^5, whereas the absolute value of that product is
less than `(1/4)16^t x^5`. The whole divisible integer is zero. Its second
factor is odd and nonzero, so `sign(c)X=2^R`.

Modulo3 fixes c>0 and X=2^R; the surviving first-index branch and the
centered strip fix k,Y>0. The exact projector now gives H|Klo. Writing
g=Klo/H and using the original integer Z/U yields

    M|Y-q^3,  Y=(2v_scale+1)q^3.

This is cancellation of a known integer factor after substitution into an
integer divisibility statement. No unproved coprimality is being assumed.
The inherited centered half-binomial recovery applies only at this late
stage, after its positive orientation and scale have been proved.

For the 15-variable common kernel and its 14/13-variable reductions, restore
the earlier degree48 B0-only source with

    h_old=Y*h_new,
    v_old=Y/q,
    n_old=Z/U-Klo/H-v_scale.

All three quantities are integers. The old scale is q*v_old=Y; its k is
`R+1+h_old XY=k`; and its normalized carrier equals the new Z/U. Its strong
and auxiliary rows are unchanged. Fresh ternary witnesses represent the
positive integer B0. This is a literal source zero.

In particular there is no assertion that a zero with Budget6>0 has
Budget8>0. That implication is unnecessary and has not been used.

Conversely the authentic canonical source has
`k=2psi_(2ell+1)((R+1)/2)`. The recurrence congruence gives
`4ell|(k-R-1)`, so the new h=(k-R-1)/ell is integral. The old canonical
family has Budget8>0 and hence Budget6>Budget8>0. Fresh guard witnesses
complete the converse with all canonical Pell values unchanged.

## 4. The 14-variable degree82 norm reduction

The final polynomial is

    P82=(Acar+1) Sunit (N+1)-1,
    Sunit=f^2-Delta I^2,
    Bg=Budget6-p1^2-p2^2, G=4Bg-3,
    delta=Q-1, Cy=QV^2-1,
    K=delta(s(s+1)-Bg+1)-Cy,
    N=K^2-G delta Cy.

At a zero the three factors are integer units. Acar is a square modulo4,
so Acar+1 cannot be -1. Delta is 0 or3 modulo4, which makes Sunit != -1.
Therefore Acar=0, Sunit=1, and N=0. Since Sunit=1 gives
`Q=Delta^2 I^2`, Q is either0 or at least9. Thus delta is nonzero even
before c and I have been recovered as nonzero by the common kernel.

The precise algebraic lemma is, for an integer d!=0,

    [d(s(s+1)-b)-e]^2-(4b+1)de=0

if and only if there are integers g,u satisfying

    g^2=4b+1,  d u^2=e,  2s+1=g+2u.

Indeed, setting x=2s+1 gives the exact identity

    16N=[d(x^2+4b+1)-4e]^2-4d^2 x^2(4b+1).

Since x is odd and nonzero, this forces a rational square root g of the
integer 4b+1; every rational square root of an integer is integral. Then
g is odd and u=(x-g)/2 is integral, and substitution gives d u^2=e.
The reverse implication is direct substitution. No sign assumptions on d
or e are required.

Apply it with b=Bg-1, d=delta, e=Cy. Then p3=(g-1)/2 and y=u-V
restore the common kernel. Conversely its zero gives s=p3+V+y.
This validates both directions, including possible zero or negative
intermediate values before the positivity guard is restored.

An independent leading-form derivation also verifies exact degree82. Put

    q0=6 beta j, X0=12q0w, Y0=v,
    R0=-q0^3(12wC-q0z), k0=R0+hX0Y0^2,
    T0=cone_A^2 Y0^2(12wC-q0z)^2+4q0^2Y0^4+q0^6.

The degree16 budget form is `-k0^2 T0`. In the leading degree22 carrier,
the coefficient of n is `256q0^6 X0^3Y0^4 k0`. The degree12 strong form
is `-4X0^2Y0^2 r^2c^4`. The degree48 N form is
`X0^4Y0^4 f^4 k0^4 T0^2`. The coefficient of the actual degree82 monomial

    j^47 w^9 v^10 z^5 f^4 r^2 c^4 n

is consequently `-2^75 3^56 beta^47`, which is nonzero for the authentic
fixed beta. This proves attained degree, not just a circuit degree bound.

## 5. The 14/90 and 13/152 companions

For P90, Fs=1+Delta I^2 is positive and 0 or1 modulo4; G is1 modulo4.
The primitive norm N is therefore not -2, while Acar+1 is again not -1.
The three-unit product forces both norms to zero and the auxiliary factor
to1. The same odd-carrier lemma, now with d=1,e=Fs, restores f and p3.
No additional bound on Y is involved in this algebraic reduction.

For P152, the retained three-root merger requires U!=0, Dt>=1 odd,
Fs>=1, and G=1 modulo4. These hold unconditionally for the new front:
ell is divisible by8 and Dt=1+ell(ell+1)k^2. The weighted roots 1,2,4
are separated by parity. First, N is a square modulo4, so N!=-2;
the unit product therefore forces N=0 and the auxiliary residual to0.
If G were negative its sole nonzero imaginary
term could not cancel; for positive radicands, distinct squareclasses
are linearly independent, and equal nontrivial classes cannot cancel
because the three coefficients have distinct 2-adic orders. The merger
restores the roots and its integral carrier translation. The common
kernel proof above then applies.

The unchanged algebraic mergers are therefore valid for the new k and
Budget6, with respective exact degrees90 and152 as checked in the
component's attained-coefficient ledger.

## 6. The 11-variable degree298 scalar endpoint

This endpoint needs a separate semantic audit because it has a different
carrier and does not restore the odd-multiplier strong witness directly.
The retained linear-cofactor proof was read for this review.

The changes preserve all its unconditional sign and parity facts. In
particular q^6, like q^8, is divisible by16, so

    D=Budget6-4 is8 or12 modulo16.

D is nonzero and nonsquare, and Pg=Dt(1+D Dt s^2) is nonzero and1
modulo4. The quintic carrier Ac is nonzero, so every zero has S,s,r,B
nonzero. The radicand `Da=(Q-1)(QV^2-1)` is positive. The even radical
weight32 preserves the source's squareclass extraction: its coefficient
is even and the other radical has odd coefficient. The only possible
two-negative-radicand cancellation would require `1024B=Pg`, impossible
modulo4. Thus both radicands are positive squares.

The source's pairwise coprimalities of B,Df,Da are literal identities and
do not involve the old guard. They force |B|,|Df|,Da to be squares;
`Df=1 modulo3` excludes a negative square. Consequently B=u^2,Df=f^2,
and Dt=tau^2 with positive roots. The Pell guard gives Budget6>=12,
which supplies B0>0 and the new early bound |Y|>|q|^2.

The adjacent-coefficient denominator descent yields the integral auxiliary
root. With I=c^2u and T_old=uT, the strong norm and both auxiliary residues
are exactly those needed by the nonodd signed-rank theorem. In particular
the proof does not assume I/c^2 odd. The even-weight norm gives S|Ac.
The carrier valuation argument then yields

    M|H(Y-q^3),  H|q^15 Kq^5.

The first gives even Y, and the common full-modulus bootstrap in Sections
1--2 applies verbatim to recover p=R and 2n0=R+1. The scalar fifth-power
projection uses x>=2^64 and t>=36, both implied by the authentic mask
bound. Its estimates are

    |q|^15 |Pi|^5 < 2^(20t-10)x^25,
    |H| > x^(t+1)/2^t.

The inequality follows from `64(t-24)-(21t-10)=43t-1526>=22`.
Therefore Pi=0, orientation is recovered, and the scalar source restores
the cubic scale. It then constructs fresh odd strong witnesses for the
native Q41 handoff. That handoff must also set `h_old=Y*h_new`, so that
the old source computes the same k. There is no use of Budget8 positivity
for an arbitrary new zero.

Completeness retains the source's exact order of choices. First use the
canonical outer data with integral new h and Budget6>Budget8>64. Choose
the Pell guard pair for D Dt. Then choose one fixed strong pair with
`4s A d c^2|I`, define u and r, choose the intersective-quintic residue,
and interpolate T_old modulo u s r using that same pair. No strong pair
is reselected after interpolation. Finally

    n=Ac/S+32ufy+tau g-Psi

is integral and makes one norm factor vanish. The additional center term
`-16r c^4 Us^2 T` is an integral polynomial independent of n, and hence
is a bijective shear of n for fixed outer coordinates.

The center cancellation was independently re-expanded by the reviewer-local
script. With weights (3,1,1,1,5) on (A,c,r,T,R), it verifies every one of
475 coefficients of Dcenter and 924 coefficients of Ecenter. Their exact
weighted degrees are80 and108. After substitution the norm's inner sum
has degree at most148, so its square has degree at most296. The product
correction has attained degree176+122=298. This proves the exact endpoint
degree298 without treating the syntactic degree352 as the actual degree.

## 7. Finite verification record and limitations

`audit_rebased.py` is written separately from the producer and the component
checker, and imports neither. `REBASED_CHECK.json` records:

* exact DAG topology, liveness, variable leaves, fixed coefficient leaves and
  operation recounts for all four equations;
* exact free-polynomial checks of ell, k and Budget6 in each actual DAG;
* the complete primitive odd-carrier identity;
* exact independent expansion of both scalar center remainders, equality to
  every supplied coefficient, and both full weighted leading forms;
* SHA256 pins of the four reviewed equation JSON files.

The component checker was also read and replayed, independently of its
producer. `REBASED_COMPONENT_REPLAY.json` records its successful checks of
all named registers, coefficient reconstruction, inherited source pins,
attained-degree ledgers and targeted corruption controls. Its large gate
ledger is optional evidence; the compact reviewer receipt is sufficient
to identify the exact files and the independent finite scope.

The reviewer script is portable. In a release with the component in
`signed/`, it can be placed in `review/` or `code/` and run directly. An
explicit `--component PATH` also works. It is read-only unless a
`--receipt PATH` is supplied, and writes no source or equation files.

Finite algebra verifies transcription and identities. The semantic audit
above verifies the new reduction and its dependency order. Neither is a
finite substitute for the explicitly retained unbounded source theorems.
