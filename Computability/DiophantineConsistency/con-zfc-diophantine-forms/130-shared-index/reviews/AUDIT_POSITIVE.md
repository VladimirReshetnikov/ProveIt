# Independent mathematical audit of the positive quotient chart

## Verdict

The 86-operation quotient-and-absorbed-padding construction is a sound
existence-preserving change of the pinned ten-positive coprime-fusion
equation. Its proof must use the direct transport argument below; the
algebraic identity alone is insufficient because `n_old=n_new-s` need
not be positive. The 87-operation unabsorbed chart does have the direct
positive-zero bijection. The consistency calibration remains inherited.

This review concerns the literal circuits under `../positive/`.
The initial working copies contained inherited metadata that was stale
after changing the graph. The packaged objects have corrected metadata;
`../positive/verify.py` confirms equality with the deterministic builder,
checks their live topological rows, and independently establishes the
claimed 86/87 operation counts and exact-degree certificates.

## 1. Exact carrier identity

Write `g=q-1`, `U=mu^2`, and let `K` denote the old `Kpos`. All other
kernel abbreviations are unchanged after substituting `Y=q^3 s`.
The old normalized center is

    n_old + V + Gamma + K/H + Y/q^3 - W B/g - e/U,
    W=1+g b.

For the absorbed chart put

    M'=g U H,
    Z'=g U[H(n+V+Gamma-bB)+K] - H(U B+g e).

Then

    Z'/M'=n+V+Gamma+K/H-WB/g-e/U.

The substitutions `Y=q^3s`, `n_old=n-s` give exactly
`M_old=q^3M'` and `Z_old=q^3Z'`. The two-root finalizer

    N=(delta Z^2-M^2 Dnum-delta M^2 a)^2
       -4 delta M^4 a Dnum

is homogeneous of degree four in `(Z,M)`. Therefore the exact integer
polynomial identity is

    N_old(Y=q^3s,n_old=n-s)=q^12 N_new.

For the unabsorbed chart, replace `n` in the displayed `Z'` by `n+s`.
There the identity uses `n_old=n` and the retained old theorem
`q^3 | Y` gives a positive-zero bijection.

## 2. Why the absorbed chart is sound

The old root extraction, coprime splitting, adjacent-Pell descent,
folding and auxiliary-index gap do not use positivity of the padding
coordinate. They depend only on the other positive inputs and on the
rational center. They therefore apply to the new center directly.
They recover the signed roots and the pre-transport bounds

    tau f < b/2,       0<y-V<b/4,       e/mu^2<b/4,

together with `Kpos>0`. The sharp-center variant has an additional
nonnegative `Gamma`; the uncentered variant has `Gamma=0`.

If `B<=-1`, solve the new normalized center for its positive `n`:

    n=(epsilon tau f-Gamma)+(nu y-V)-Kpos/H+WB/g+e/mu^2
      < b+WB/g.

Since `W=1+g b`, the assumed sign gives
`WB/g <= -b-1/g`, hence `n<0`, a contradiction. Thus `B>=0` and
the same source-side sign/rank bounds follow.

After `p=R`, the old odd-index argument supplies parity and licenses
`gcd(mu^2,gH)=1`. Separating the `mu^2` denominator gives `mu^2|e`.
The first index and ratio/growth proof are unchanged. Separating `H`
gives the stronger statement `H | g Kpos`, so the old whole-product
projection follows with a smaller prefactor. Its upper bound is
strictly no larger than the already proved `q^3g` prefactor bound.
Consequently `X=2^R` and `Kpos/H` is integral. The remaining fraction
gives `g | W B`, hence `g | B`, because `W=1 mod g`.
The old condition `q^3|Y` is built into the new chart.

All later parity, half-binomial and fresh unscaled-source reconstruction
steps use these recovered outer facts; none requires the old padding
coordinate to be positive. They consequently yield the same finite
syntactic refutation from every new positive zero.

## 3. Completeness

From a finite refutation choose the old canonical positive tuple, whose
`Y` is divisible by `q^3`. Set `s=Y/q^3>=1` and
`n_new=n_old+s>0`, retaining all other coordinates. The exact carrier
and finalizer identities give a new zero. This is sufficient for
existence equivalence. A positive pointwise inverse for every arbitrary
new tuple is neither needed nor asserted.

## 4. Independent exact-degree proof

Count every new quantified input with degree one. After `Y=q^3s`,

| Register | Degree |
|---|---:|
| `q,X,mu,Y` | `1,2,2,4` |
| `A,Delta,H` | `8,16,8` |
| `c,D,E` | `5,30,11` |
| `F_s,Q=delta,b,V,M'` | `68,84,6,74,13` |
| `a=D F_s`, sharp `Gamma=A D E` | `98,49` |

The leading part of `b=c(T+alpha)-R` is now `c_0(T+alpha)`.
It is **not** `-R_0`, which was the leading part before this change of
coordinates. Put `Z0=Z'-M'(V+Gamma)`; its degree is at most 21.
The old exact centered finalizer identity gives the uniquely highest
term

    4 delta^2 M'^4 V^2 (Gamma^2-a).

For `Gamma=0` its degree is
`2*84+4*13+2*74+98=466`.
For the sharp center,
`Gamma^2-a=D^2E^2-D` has degree 82, giving degree 450.
All other terms in the centered identity have smaller degrees:
the auxiliary bracket has degree at most 208 (uncentered) or 192
(sharp), and its square and mixed terms are below the respective
claimed top degree.

Writing `q0=beta J` and `k0=eta+zeta`, the complete leading forms are

    uncentered:
      -2^10 q0^326 i^10 w^30 s^64 k0^34(T+alpha)^2,

    sharp:
       2^10 q0^314 i^10 w^28 s^62 k0^34(T+alpha)^2.

Both are nonzero for the actual fixed nonzero `beta`. This proves exact
degrees 466 and 450, not merely syntactic degree bounds or degrees on
sample lines. Absorbing `s` into the padding changes only a lower-degree
term and preserves both leading forms.

## 5. Comparison

The 86/466 equation improves the operation count of the inspected
89/288 positive endpoint while increasing total degree. This is an
honest operation/degree tradeoff. The 89/450 sharp quotient companion
is dominated on these two measures by the older 89/288 endpoint and
should be presented as an algebraic control, not a new Pareto record.

The actual fixed coefficient tuple, its calibration, and the distinction
between ten positive unknowns and unrestricted integer unknowns must
remain explicit in the final report.
