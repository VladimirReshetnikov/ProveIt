# First-index and rank-congruence boundary for residue 82

This is an exact **partial assignment**, not a graph zero. It strengthens the
[smaller first-norm control](../ordinary13-residue82-firstnorm-companion-obstruction/):
it satisfies the actual 82 first norm, positive q³ scale and residue carrier,
the scalar rank window, and the early `q⁴` rank/index congruence with a first
Pell index at least 13. Nevertheless the corresponding 84 companion carrier
is zero and `X<q²`. A nonzero strong residual modulo a small prime proves that
the complete 82 output is nonzero. No claim is made about a full zero, global
zero existence, the actual compact44 coefficients, or iPRA.

## Symbolically defined positive tuple

Use the toy ports and fixed inputs

```
beta=46, K0=0, MC=MF=1, J=1, q=47,
F=1, alpha=45, X=47, s=1, Y=q³, m=X*Y²=q⁷,
R=4771536, n=(R+1+q⁴)/2=4825609.
```

Let `D=m*(m+1)` and define model-natural integers `(tau_j,k_j)` by the
ordinary Pell recurrence

```
(tau_0,k_0)=(1,0)
tau_(j+1)=(2*m+1)*tau_j+2*D*k_j
k_(j+1)=2*tau_j+(2*m+1)*k_j.
```

Set `tau=tau_n`, `k=k_n`, `ell=m*k`, `eta=1`, `zeta=k-1`, and
`r=k*(46-1)+1+tau-ell`. Take `f=2`, `i=T=y=gamma=1`. No enormous integer is
materialized by the checker. All inputs are positive: the recurrence has
`k>=2n>2` and `tau>m*k` for n>0, as follows from positivity and its norm.

The first norm holds **exactly** because the recurrence preserves
`tau²-D*k²=1`. The residue carrier has `C=1`, `Pprime=46=b`, and the chosen
r makes `Z=b*tau`; hence its first residual is zero. The companion carrier is
`B=(q-F-alpha)*(X+K0*q)-F*q=0` and `X=q<q²`.

The recurrence also has natural witnesses h_j,w_j for the exact invariants

```
tau_j = 1+2*m*h_j,       k_j = 2*j+4*m*w_j.
```

They start at zero and are preserved by the recurrence; `check.py` verifies
the explicit update identities as free-ring polynomials. Since `q⁴ | m`,
`k ≡ 2n ≡ R+1 (mod q⁴)`. In particular, the q⁴ signed rank congruence,
`n>=13`, the first-index residue form `k=2n+4m*w`, and the scalar rank window
all hold, with `2n=R+1+q⁴` rather than the later exact-index conclusion
`2n=R+1`. These are the listed partial facts only; the construction does not
supply the main Pell, strong, auxiliary, exact-index or full-zero hypotheses.

## Finite certificate and limitation

The checker pins both graph JSONs, proves norm and residue-invariant
polynomial identities, and uses 23 binary-exponentiation steps modulo
`4m` and 1,000,003. It evaluates all graph rows modulo the latter prime:
`A0=0`, `g72=330566`, and `out=937166`. Thus `g72` and the complete output
are nonzero over the integers, without computing the multi-million-step Pell
integers. A standard natural-number model already witnesses that the displayed
partial assumptions cannot by themselves force B>0 or X>=q²; stronger
full-zero hypotheses or another witness map remain open.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B research/ordinary13-residue82-firstindex-companion-obstruction/check.py`
and compare with [result.json](result.json). No Lean process is run.
