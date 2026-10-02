# Independent audit: the explicit finite-height radius constant

Audit date: 2 October 2026. Audited source: `../a202061-second-order-research/finite-height-explicit-constant.md`. This is separate from the main coefficient-deficit audit. All frozen reports remain unchanged.

## Verdict

The argument proves

log(rho_H/rho)=alpha/H [(1/2)log H+loglog H+c_*+o(1)],

where

c_*=log((1-m_*)/(2a_*)),
m_*=rho/((1-rho)z+rho),
a_*=rho C_q/((1-rho)z),
C_q=sqrt(-16z^2+55z-10)/(2sqrt(pi)).

The numerical value is c_*=0.8667962458055399529886348076493373710016.... I found no unresolved amplitude, moment, boundary, or spectral-comparison gap. The unrestricted-destination row threshold has the same constant, and the proof establishes the equality with the finite-height spectral threshold rather than merely assuming it.

This is not a determination of the constant inside the global coefficient deficit's O(F/log n) remainder.

## 1. Independent amplitude derivation

For the exact quadratic

xT(1-zeta)Q^2+B(x,zeta,T)Q+(1-x)zeta=0,

write Delta for its discriminant and z_c for its smaller root. The branch with Q(0)=0 is

Q=[-B-sqrt(Delta)]/[2xT(1-zeta)].

The singular coefficient of (1-zeta/z_c)^(1/2) is

-sqrt(-z_c Delta_zeta(x,z_c,T))/[2xT(1-z_c)].

Because [zeta^q](1-zeta/z_c)^(1/2) is asymptotic to -z_c^-q q^-3/2/(2sqrt(pi)), the fixed-q amplitude is

C_q(x,T)=sqrt(-z_c Delta_zeta(x,z_c,T))/[4sqrt(pi)xT(1-z_c)].

This fixes both the sign and the factor of two independently. At x=rho and T=1/z, the squared amplitude reduces exactly modulo z^3-5z^2+6z-1 to

C_q^2=(-16z^2+55z-10)/(4pi).

The positive root is selected because all transfer amplitudes are positive at the real critical point. The accompanying independent script `check_finite_height_amplitude.py` performs this algebraic reduction and evaluates m_*, a_*, and c_* to forty digits. Its successful output is saved in `finite-height-amplitude-output.txt`.

The actual macro-kernel amplitude is a_*=rho T C_q/(1-rho). The additional T factor is required by d=1+r-q and is correctly present. The leading macro factor is the full x/(1-x), also correctly present.

## 2. Uniform transfer and differentiability

At the critical point, the smaller discriminant root, larger root, and pole at 1 are strictly separated. In a fixed small complex parameter neighborhood these separations persist in modulus after scaling zeta by z_c. The explicit quadratic expression is an analytic factor times (1-zeta/z_c)^(1/2), plus terms analytic in a larger disk. Uniform singularity expansion therefore gives

A_q(s,theta)=a(s,theta)q^-3/2 exp(qPsi(s,theta))(1+E_q(s,theta)),

where E_q is analytic and uniformly O(1/q) in that neighborhood. Cauchy's formula on a smaller fixed neighborhood bounds the first four derivatives of E_q by O(1/q) as well. This is the derivative statement needed for logarithmic moment generating functions; it does not require dividing by a possibly vanishing derivative of the leading term.

Finitely many q are handled directly in the common analytic domain eta=x^2T/(1-x)^2<1. The root derivative identities from the frozen certificate give Psi_s=1/alpha, Psi_theta=0, and Psi_thetatheta=nu=v/alpha. Hence at s=O(log H/H), the fixed-q mean is O(1+qs), variance is nu q+O(qs+1), and the remaining cumulants used are O(q+1), uniformly for q<=H.

## 3. Endpoint sum and the full critical mass

For k=H Psi(s_H(c),0), the uniform expansion gives

k=(1/2)log H+loglog H+c+o(1).

The q<=H/(log H)^2 range tends to the complete critical row mass m_*: fixed q converge, and the rest of this range is uniformly dominated by a constant multiple of q^-3/2. The middle range up to H/2 is o(1). For q>H/2, writing q=H-r gives

sum q^-3/2 exp(kq/H)
 =H^-1/2 exp(k)/k (1+O(1/k)+o(1))
 ->2exp(c).

The expected r in the geometric endpoint window is O(H/k), so the factor (1-r/H)^-3/2 changes the sum only by relative O(1/k). This justifies the prefactor 2. There is no double counting of critical mass, since the critical tail q>H/2 vanishes.

Removing the top W terms changes this sum by O(W log H/H), which tends to zero for W=H^gamma, gamma<1. Thus the row sum with q<=H-W still tends to m_*+2a_*exp(c). Monotonicity in the length tilt supplies the row-threshold expansion.

For c<c_*, all finite-height rows are bounded above by this unrestricted-destination row sum, so the Perron radius is below one. This gives the correct lower bound on rho_H.

## 4. Moments for the homogeneous high-strip kernel

For c>c_* and Q=H-W, the homogeneous increment weights a_d formed from all q<=Q have total mass R tending to a number greater than one. The fixed-q mean estimate yields sum a_d d=O(log H), since R=O(1).

At theta=+/-c1/sqrt(H), the logarithmic moment generating function at fixed q differs from its value at zero by

O(qs/sqrt(H)+q/H+H^-1/2)=O(1).

Consequently sum a_d exp(c1|d|/sqrt(H))=O(1). This proves all the asserted upper moments and the exponential tail bounds. The lower second-moment bound follows because a positive fraction of the endpoint mass lies in q between H-O(H/log H) and H-W, where the conditional variance is at least a positive constant times H. Thus sum a_d d^2=Theta(H).

Spending half the exponential moment gives, for r=0,1,2,3,

sum_{|d|>W}a_d |d|^r <=C_r H^(r/2) exp(-c2 W/sqrt(H))=o(1).

These estimates hold for every fixed gamma in (1/2,1), which is exactly the range used later.

## 5. Exact sine centering

With delta=pi/(W+1), the truncated sum

S(tau)=sum_{|d|<=W}a_d exp(tau d)sin(delta d)

has positive derivative: d sin(delta d)>0 for every nonzero retained d. Taylor's inequality for sine, the mean bound, and the third absolute moment give

S(0)=O(delta log H+delta^3 H^(3/2)).

A fixed sufficiently large B retains a positive fraction of the second moment inside |d|<=B sqrt(H). For |tau|<=epsilon/sqrt(H), the exponential factor there is bounded below, and delta B sqrt(H) tends to zero. Hence S'(tau)>=c delta H throughout this interval.

The ratio of the last two bounds is

O(log H/H+sqrt(H)/W^2)=o(H^-1/2).

The intermediate value theorem therefore gives a unique zero tau_H in that interval, with precisely the stated bound. The derivative estimate justifies both signs of the bracketing argument; no assumption about the sign of the original drift is needed.

The corresponding cosine sum satisfies C_H=R+o(1). Indeed the omitted tail is o(1), the exponential reweighting costs O(|tau_H|sqrt(H))=o(1), and the cosine error costs O(H/W^2)=o(1). Weighted moments under tau_H remain bounded by the same exponential-moment argument.

## 6. Boundary-safe Perron comparison

Index the strip by 1,...,W and put f_i=sin(pi i/(W+1)), extended by zero outside. For a retained |d|<=W and i in the strip, i+d lies between 1-W and 2W. Outside the strip, sin(delta(i+d)) is nonpositive throughout that range. Therefore

f_{i+d}>=sin(delta(i+d))

is valid even at both strip boundaries. Summing and using S(tau_H)=0 gives

(B_H f)_i>=C_H f_i

for every i, with no division by a small sine value and no uncontrolled endpoint error. This is the decisive improvement over a row-only or approximate-centering argument.

All q<=Q are legal at every source height in the strip. Thus B_H is a restriction of the original finite-height kernel followed by positive diagonal similarities using t and exp(tau_H). Spectral-radius monotonicity and Collatz-Wielandt give

r(K_H(x))>=r(B_H)>=C_H=R+o(1)>1.

This proves the upper bound on rho_H for every fixed c>c_*. The frozen finite-matrix theorem supplies the exact identification of rho_H with the unique positive x where the Perron root is one. Letting c approach c_* from both sides proves the claimed explicit expansion.

## Conclusion

The amplitude and the narrow-strip spectral argument have now been separately checked beyond the original leading-theorem audit boundary. The explicit finite-height constant can be included in a new result package, provided its scope remains distinct from the global deficit's still-undetermined F/log n constant.
