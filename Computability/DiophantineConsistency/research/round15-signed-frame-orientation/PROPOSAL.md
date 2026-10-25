# Recovering the sign of the common Round15 Pell center

Status: independently checked ordinary proposal, conceptual only. No source
graph, compiler, projected equation or metric is generated here. This note
replaces the positive-center step of the separate factorial-output-guard
argument; that argument's current proof/checker retains A>=0 and does not
already license this extension.

The proposed integer system keeps the entire principal Round15 body and all
its other predicates, but omits the scalar F>=0 and scalar A>=0 predicates.
The F omission is the separately reviewed staged lead. This note proves both
F>=1 and A>=2 directly before invoking the old whole-source theorem. All
existing remainder anchors, t/K ordinate slacks, frame Zminus1, common
Vaux-1 and q4minus1 predicates remain available. This is a whole guarded-body
zero-existence argument with fresh guard witnesses, not a predicted saving
in a projected equation.

The theorem is JOINT redundancy of these two predicates from the remaining36
original predicates. It does not compose the F-only theorem while its retained
A>=0 premise is missing. In both possible signs of A, the t argument below
recovers F first; the even-K argument then excludes A<0. Only after both
conclusions are established are two fresh Legendre triples supplied.

## Fixed source boundary

The source is the original principal Round15 archive, Git commit
5f3379063df18910a981d2e6cae6aee91b79cf4d, ZIP SHA256
1be83b372f888f8349b2f231978541bc872f4b5e4be9b4a3429a3d5b7016f3b2.
Its direct/unified_reparam_derived_shell/source.json has SHA256
0b36a5ff088aece09f23dff8f55a2c6904e1f69615f16c4a5299acb1fa790c67.
The unchanged exact body and transformation interfaces were independently
reviewed/reproduced in research/round15-direct-reproduction, closed at
42d21797debe14e300b33735a83363022d00008d884c35805c25d820d3e0e3e1.
No frozen source or factorial-output-guard file is edited by this proposal.

The actual relevant coordinates are F=3,B=5,V0=6,N=26,q=179,L=181,
W=245,A=246,Zminus1=247,U=250,Vaux=251,q4minus1=252.
The undoubled t pair is257/258 with retained slack261; the undoubled K
pair is274/275 with retained slack278. Crucially both K power requests use
that same274/275 pair. Their congruence rows are239 and244.

The initial literal cuts need neither F nor A sign:

* factorial row3: B=fact_remainder+fact_slack+1>=1;
* digit-bound row167: q=B+choose_oslack+1>=2;
* remainder-bound row166: L=q*choose_u+choose_slack+2>=2;
* t=16+t0>=16, and row210 gives Y_t=t+slack_t>=t;
* endpoint row7: y=F+endpoint_r0+1, used only after recovering F;
* row10: R=18+t0+x+y+F, and K=2R, used only after recovering F.

All scalars on the right of the first four inequalities, except the already
bounded B/q, retain their direct predicates. No power, other seed positivity,
weighted-pair restoration or factorial meaning is used in these cuts.

## The frame and the common index work with a=|A|

The unchanged frame identity is W=2*(2+sum(atom^2)), using the37 actual
original power atoms. Thus W>=4, |atom|<W,2|atom|<W and atom^2<W without
any atom sign premise. The frame norm and retained Zminus1>=0 give

    A^2-W^3*(W+2)*(Zminus1+1)^2=1.

Put a=|A|. This excludes A=0 and classifies the positive pair
(a,W*(Zminus1+1)) at Pell center W+1. Its index is a positive multiple of W,
exactly as in the old argument. Consequently

    a>W^W and a>W^2.

This statement never assumes A>=0. In particular a>=2. The unchanged common
norm U^2-(a^2-1)*Vaux^2=1 and retained Vaux>=1 imply
|U|=chi_a(h), Vaux=psi_a(h) for a positive common index h.

The unchanged whole15-seed product identity and Vaux>0 imply every seed
ordinate Y_i is nonzero and Y_i^2 divides Vaux. They also imply the omitted
common product quotient is nonnegative. The comparison center, denoted Cstar
here to distinguish it from factorial B, satisfies

    Cstar=1+4*Vaux*(q4minus1+1)>=5,
    Cstar=A modulo U,   Cstar=1 modulo 4|Y_i|.

These conclusions do not use F, A or any seed exponent sign.

For a positive requested undoubled exponent k with retained Y>=k, classify
the main pair as |X|=chi_a(i),Y=psi_a(i), i>=1. Squared divisibility yields
i<=h and Y divides h. Classify its comparison norm at positive center Cstar
with index j. Write sigma=sign(A). Polynomial base transfer gives

    chi_Cstar(j)=chi_A(j)=sigma^j*chi_a(j) modulo U.

The existing independent abscissa signs absorb sigma^j. Hence the usual
abscissa congruence yields j=+/-i modulo2h. The ordinate congruence and
Cstar=1 modulo4Y give j=+/-k modulo4Y. Reducing both modulo2Y gives
i=+/-k modulo2Y. Since1<=i<=Y and1<=k<=Y, this forces i=k; the possible
minus endpoint has i=k=Y and gives the same conclusion. This replaces the
old positive-A indexed-Pell step without changing any source row.

Only the t instance is used before F recovery. The K instance is used after
K>0 has been independently recovered. No general positivity theorem for
the other13 seed exponents is invoked in this preliminary argument.

## A signed-base, signed-center small-residue lemma

Let A be either sign with a=|A|>W^W and a>W^2. Let n be any nonzero integer
with |n|<W, let1<=k<W, and let the candidate m be an integer with |m|<W.
Set P=n^k and

    T=2*A*n-n^2-1.

Then |T|>a. Indeed, writing r=|n|:

* if A*n<0, |T|=2*a*r+r^2+1>a;
* if A*n>0, T=2*a*r-r^2-1>=2*a-2>a, since1<=r<W<a
  and this quadratic is increasing on that integer interval.

In particular T is nonzero. There is no assumption n>0 or T>0.
The elementary frame estimates give

    |m+/-P| <= W-1+(W-1)^(W-1) < W^W < |T|,
    |m*P+/-1| <= (W-1)^W+1 < W^W < |T|.

Define signed-center canonical Pell coordinates

    xA=chi_A(k), yA=psi_A(k),
    H=xA+(n-A)*yA, J=xA-(n-A)*yA.

Their polynomial recurrence is valid for all integer A,n. It gives
H=P modulo T and H*J=1+T*yA^2, so J*P=1 modulo T. Once the absolute index
is k, all four possible main quadrants can be written X=epsilon*xA,
Y=delta*yA. The literal power congruence therefore has exactly these cases:

| epsilon | delta | residue implication | exact small-residue consequence |
| --- | --- | --- | --- |
| +1 | +1 | T divides m-P | m=P |
| -1 | -1 | T divides m+P | m=-P |
| +1 | -1 | T divides m*P-1 | m*P=1 |
| -1 | +1 | T divides m*P+1 | m*P=-1 |

If |n|>=2, then |P|>=2 and the last two consequences are impossible over
integers. This is a universal bound and recurrence proof, not a sampling
claim. It applies in particular to the later negative base N.

## Negative A is incompatible with the two retained-index requests

Suppose for contradiction A<0. The previous frame/common-index discussion
is still valid with a=-A. At the t seed, k=t>=16 and Y_t=psi_a(t)>0.

For negative A,

    chi_A(k)=(-1)^k*chi_a(k),
    psi_A(k)=(-1)^(k-1)*psi_a(k).

The supporting t request is the actual q^t call, with q>=2 and L>=2.
If t is even, positive Y_t is -psi_A(t). Its two possible X signs give
either L=-q^t<0 or L*q^t=1. Both are impossible. Thus t is odd. For odd t,
positive Y_t is +psi_A(t); the only possible X is chi_A(t)=-chi_a(t), and
L=q^t. The other quadrant would give L*q^t=-1. The actual t pair is
therefore the signed-A canonical pair, despite having a negative abscissa.

Call0 shares this pair. Its base is F^2+1>=1 for every integer F. The
canonical-pair congruence and the same small-residue bound give exactly

    V0=(F^2+1)^t>0.

No inverse-quadrant exclusion at base1 is needed: the pair has already been
oriented by q>=2. The raw identity F*B=V0+fact_slack and B>=1 now force
F>=1. Moreover V0>=F^2+1, so B>F>=1, B>=2 and q>=3. Endpoint row7 then
gives y>=1. With retained x>=0 and t0>=0, R>0 follows from row10. Thus
K=2R is a positive even integer, before any K power is interpreted.

Use the retained K slack and the absolute-index argument to obtain
Y_K=psi_a(K)>0. Since K is even,

    chi_A(K)=chi_a(K)>0, psi_A(K)=-psi_a(K)<0.

The first K request, row239, has base B>=2 and candidate N. Positive Y_K
is -psi_A(K). Its two possible abscissa signs give either

    N*B^K=1, or N=-B^K.

The first is impossible over integers. Hence

    N=-B^K<=-4,
    (X_K,Y_K)=(-chi_A(K),-psi_A(K)).

The second K request, row244, uses this SAME pair, with the actual signed
base N and positive output q. Both |N|<W and K<W follow from the original
frame atom list. The signed-base lemma is applicable without claiming N>0.
Its fixed (-,-) quadrant now forces

    q=-N^K<0,

because K is even. This contradicts q>=3. If one instead enumerates both
quadrants afresh for this request, the other possibility q*N^K=1 is likewise
impossible; shared-pair binding makes the fixed-quadrant argument stronger.
This excludes every A<0 branch. Together with the frame bound it proves A>=2.

## Completing the staged guard restoration

For A>0, the retained positive t ordinate and the q>=2,L>=2 request orient
the t pair in the usual positive-center way. Call0 and the raw factorial
rows then give F>=1 by the same argument. Thus every zero of the proposed
guard-reduced body has both missing scalar targets nonnegative. Choose fresh
Legendre triples for F and A. All other body coordinates and guard witnesses
remain unchanged. This gives a zero of the exact already reviewed original
guarded principal source, so its full ordinary calibration applies.

Conversely, every zero of the original guarded source gives a zero of the
proposed system by forgetting just those two guard triples. Existing canonical
completeness already chooses A>0 and F>0, so no new private Pell witness
construction is needed for this direction. These are existential guard-witness
maps at a fixed entire body tuple, not unique maps of all witness triples.

No broad early sign-closure replay is presumed after deleting A/F: the proof
above uses only the explicitly retained cuts, frame/common-index identities,
t helper and then the two K requests. After both signs are restored, the old
whole sign closure, all13 even-seed arguments, all18 powers, weighted interval
guards, factorial/binomial/CRT/source semantics can resume unchanged.

A future literal candidate still requires a complete source/guard delta,
checked reconstruction of all source ports, ordinary peer approval and actual
projection/whole-coefficient certificates. This note supplies only the ordinary
orientation lead. It makes no operation, variable, degree or height claim.
