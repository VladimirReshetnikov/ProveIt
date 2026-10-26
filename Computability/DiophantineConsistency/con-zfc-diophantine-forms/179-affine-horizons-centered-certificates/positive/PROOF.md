# Center the inverse-trace carrier at its polynomial square approximation

**Retained scaled-chart method control.** The bounded late source17287/214
strictly dominates this earlier operation/degree point. Principal new
89/210 and90/206 compositions are in `late172/PROOF.md`; do not treat
this earlier circuit as a current Pareto claim.

## Result and exact scope

The supplied literal circuit has **ten independently strictly positive integer
unknowns, 88 live binary integer-leaf operations, and exact degree 224**.
The pinned inverse-trace parent has 85 operations and degree 232. This is a
new operation/degree tradeoff, not a simultaneous improvement, global
minimum, or a reduction of the unknown count. All scalar multiplications
and squares are charged. The principal complete tuple remains the parent's
little-endian BFS943/radix67 tuple. `start_marker4177/` separately binds the
whole current big-endian tuple with its own native calibration and Pcs
reconstruction; no tuple is assembled port-by-port.

The change is a polynomial square approximation to the already extracted
root. Put g0=AUE. Since G=E+(A²−1)U²E², the exact identity

    g0²−G=U²E²−E

removes eight highest degrees from the final norm. Completeness uses the exact positive shift n_new=n_old+g0V at the
parent's constructed positive zeros, where V>0. Soundness is proved
separately; the inverse shift need not preserve positivity.

The retained parent is copied unmodified in `parent/`, including its full
ordinary proof, recurrence/projection sources, coefficient recipe, and
native/refutation boundary. Every inherited file is hash-pinned. The new
argument below proves both directions of this carrier change; the parent
then supplies the unchanged arithmetic-to-native implication. This is an
ordinary composed theorem, not a new end-to-end formal-kernel object,
consistency decision, claimed zero, or encoded internal-ZFC proof replay.

## 1. Entire polynomial, with no extra variables

Inputs J,F,alpha,i,T,w,s,n,eta,zeta are strictly positive integers. The four
fixed ports beta,K0,MC,MF are the whole specified tuple. Define

    h=beta J, q=h+1, C=q−F−alpha,
    X=qw, Y=qs, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A²−1, H=4A−5,
    ell=(XY)(kY), E=1+ell(ell+k),
    R=[h(q−F)+alpha](q²−1)+(MC+q MF)J,
    B=(K0+w)C−F, U=ic², a=Delta U²E,
    F0=1+a, G=EF0, f=a+F0, Q=4Delta aF0,
    b=cT−R, V=fb−c, g0=AUE,
    K=X(3c−2X)+2,
    e6=6(k−R−1)−ell(k²−4), D=6q⁶, M=hDH,
    Z=hD[H(n−V(bB+g0))+K]−H[DB+h(e6−6q⁴s)],
    P=Q(Z²−M²GV²)+(M²G−Z²).

All symbols after the ten inputs are polynomial abbreviations. In
particular g0 is not a root or an additional quantified input. There are
no division, recurrence, binomial, or variable-exponent gates in P.

For proof only define v=XY², L=bV, e*=e6/6,

    rho=e*/q⁶, sigma=s/q², t=B/h, W=1+hL,
    kappa=K/H, z=Z/M.

Before any divisibility assertion, the exact rational carrier identity is

    z=n+kappa+sigma−Wt−rho−g0V.                    (1)

Equivalently, if Z0 denotes the parent's numerator evaluated on the same
inputs, then Z=Z0−Mg0V. This is a polynomial identity, not an equality of
the new and old polynomials or their positive witness sets.

## 2. Root extraction and signed bootstrap

Everything before transport in `parent/PROOF.md` §§2–3 and
`parent/inherited_trace/PROOF.md` §§3–4 is unchanged: it uses the final
norm equation, not a particular carrier numerator. At a zero it gives
positive integers tau,f0,g,y and epsilon in {−1,+1} with

    E=tau², F0=f0², g=tau f0, z=epsilon gy,
    QV²−(Q−1)y²=1,
    f²−Delta I²=1, I=2Ug, c²|I,
    c=psi_A(p), p positive odd,
    k=2psi_(1+2XY²)(m), m>=2,
    c>8XY³, c>X, K>0.

The p=3 exclusion uses q|X,Y and remains valid. The exact trace-linear
auxiliary-index-three identities are unchanged, so b and V are nonzero
with the same sign and

    L=|b||V|>0, a>3g, f>g,
    y<(3/2)|V|, |V|>8Q²,
    |b|>8f³−1/2>8g.                              (2)

These deductions precede every assertion about B,C,R and the signs of b,V.
They also establish g as an integer; the inequalities below do not replace
root extraction by numerical tests.

The new square approximation satisfies

    g0²−g²=U²E²−E>0,
    g0²−g²<U²E²<G/Delta.

Since Delta>=3, this gives g<g0<2g. Combining with (2),

    gy+g0|V| < (7/2)g|V| < 7L/16 < L/2.          (3)

As in the inverse parent, k>=2 implies e*<=k−R−1<b. Hence
rho<|b|/q⁶. If B<=−1 then Wt<=−W/h<−L, and (1) gives

    n=epsilon gy+g0V−kappa−sigma+Wt+rho
      <L/2−L+|b|/q⁶<0.

The last inequality uses |V|q⁶>2, so |b|/q⁶<L/2. This contradicts
n>0. Therefore B>=0 and C>0. The retained mask bound now gives
3q<R<q⁴−2. Since c>2R, b,V are positive. The unchanged normalized
rank and signed auxiliary-index argument gives p=R, followed by R odd,
q even, and J odd. No negative-R case was silently excluded.

## 3. Unchanged authentication, projection and native endpoint

The exact carrier difference Mg0V is divisible by M=hDH. Thus every
numerator reduction modulo D and H in `parent/PROOF.md` §§3–4 is
unchanged. In particular the same integer cancellation of 6 gives
q⁶|(e*−q⁴s), hence q⁴|e*. The inverse-Lucas difference identity

    3(e*−(2m−R−1))=4v²[24Z_m−A_m S_m]

still holds with A_m=binom(m+1,3)+4vZ_m and
S_m=k²+2mk+4m²−4. Its prime-by-prime valuation argument gives
q⁴|(e*−(2m−R−1)). Monotonicity gives m<R, and therefore
m=(R+1)/2. It is still incorrect to conclude q⁶|e* before projection
at arbitrary q; the retained third-primary counterexample is checked.

Reducing modulo H gives H|6hK. The parent's whole-product height bound
and universal Pell projector imply X=2^R. Since q|X, q is a power of 2;
only now is q⁶|e* obtained from the inverse correction identity. Thus
rho and kappa are integers. The added g0V is an integer on every input,
so (1) yields exactly the same final integrality conclusions q²|s and
h|B. Consequently q³|Y and t=B/h is a nonnegative integer.

These are the identical outer witnesses and exact native-interface
relations used by the parent, including the fixed-minus parity,
half-binomial rounding, and fresh source reconstruction at base
Y(X+1)+2 (not the present A). The full calibrated tuple, not merely its
scalar box, gives a finite syntactic ZFC refutation. For the independently
calibrated Start-marker4177 specialization see its separate PROOF.md.

## 4. Constructive strictly positive completeness

A finite refutation supplies a parent positive zero using the exact
canonical outer data, ratio construction, permitted strong period seed,
and unsquared-trace auxiliary construction in `parent/PROOF.md` §5.
In particular its b,V are strictly positive. Keep every input except n,
and define

    n_new=n_old+g0 V.

The quantities g0=AUE and V are independent of n, are integers, and are
strictly positive at this constructed zero. Thus n_new>0. Directly,

    n_new−V(bB+g0)=n_old−bVB.

All other registers agree, so Z_new(n_new)=Z_old(n_old) and the two final
polynomial values agree exactly. In particular P_new=0. The positive
norm branch may be retained, and no additional period/cofinal choice or
new size estimate is needed. This proves strictly positive completeness
for both entire calibrated tuples.

This is a one-way map on parent positive zeros, not a bijection asserted
on arbitrary positive inputs. A new positive zero could have
n_new−g0V<=0; that is why §2 independently proves the signed bootstrap
and §3 recovers the native endpoint rather than using an inverse shift.

## 5. Literal cost and the exact degree

The parent computes L=bV, LB, n−LB in three gates. The new circuit
computes bB, bB+g0, V(bB+g0), n−V(bB+g0) in four. A=(A−1)+1
and g0=A(UE) use two more gates; UE is already live in the seed.
Thus exactly three gates are added: **88 operations: 52 multiplications,
20 additions and 16 subtractions**, integer leaves only.

Naive gatewise maximum degrees miss a genuine cancellation. Exact
polynomial identities give

    Z²−M²GV²
      =Z0²−2Mg0VZ0+M²E(U²E−1)V².               (8)

The respective degree bounds on the right are 114,133,144. They follow
from deg(Z0)=57, deg(M)=11, deg(g0)=25, deg(V)=40,
deg(U)=7, deg(E)=14. Therefore the inside has exact degree144.
Multiplication by Q, degree80, yields224, while M²G−Z² has degree152.
No leading cancellation remains.

With q0=beta J, k0=eta+zeta and
B0=k0 sT−q0²(q0−F), the full leading homogeneous part is

    [P]_224=9*2^10*q0^96*w^24*s^56*i^10*k0^32*B0².

It is nonzero at every actual beta>0. Its 202 terms are verified exactly,
not inferred from a selected numerical ray. The checker authenticates
all88 live gates through39 exact cuts, proves identity (8) and the square
remainder independently of the producer, checks the full leading form,
reconstructs the entire coefficient tuple, and rejects177 actual corruptions.
Normal and optimized Python receipts agree. Separately labelled finite
recurrence diagnostics do not prove any of the unbounded lemmas.
