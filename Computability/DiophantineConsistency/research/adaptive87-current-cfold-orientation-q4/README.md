# C-fold: positive main root and the q⁴ rank congruence

This is a standard-integer fact-level proof for the pinned current-port [88/28 C-fold candidate](../adaptive87-current-cfold88-degree28/README.md). It discharges the **orientation and q⁴ congruence cuts** listed there, with the exact hypotheses below. It does not prove the remaining index alignment, power recovery, Cal, graph zero equivalence, or an all-model/iPRA theorem. The checker pins the graph and its earlier byte-authenticated port receipt, verifies the exact main/rank row bindings, and checks the displayed main-carrier ring identity.

## Hypotheses and literal bindings

Work in standard integers. The graph's thirteen witnesses are strictly positive. The fixed port tuple satisfies `beta>=46`, `K0>=0`, `MC>=0`, and `MF>=0` (the current2011 tuple satisfies these stronger byte-checked bounds). The arguments below need only `beta>=2`; `K0` is not used by the main-carrier argument. Assume:

* The first and main square residuals vanish, `A0=A1=0`.
* `C=q−F−alpha>0`. A positive candidate zero supplies this as shown in the candidate packet; alternatively take it as an explicit fact-level assumption.

Define exactly the graph quantities

```
b=J*beta, q=b+1, M=q³*b, U=Y*q², E=X*Y,
k=eta+zeta, c=eta+Y*k, a=Y*(X+1), H=4*a+3,
Delta=(a+2)²−1,
G=alpha+(q−F)*b,
R=G*(q²−1)+J*(MC+q*MF),
Z=M*(ell+k+rho−k*C)+Y*b−q³*Bt,
Dstar=U*(X+a*c)+H*(U*gamma+E*q+R+1−k).
```

Here `ell=X*Y²*k` and `Bt=C*(X+K0*q)−F*q`; neither a sign for Bt nor positivity of an old first-coordinate substitution is assumed. The exact `Dstar` identity follows from the actual `r0=(k−R)−1` and `shift=U*gamma+E*q−r0` rows. By positivity `q>=3`, `U>0`, `k>0`, `a>=2`, and `H>0`. From `C>0`, we have `q−F>alpha>0`, so `G>0` and `R>=0` under the stated mask-port nonnegativity.

## First factor supplies q³ | Y

`A0=0` is `Z²=M²*(1+ell*(ell+k))`. Since `M=q³*b>0`, standard integer square divisibility gives `M|Z`. Reducing the displayed Z modulo q³ gives `q³ | Y*b`; consecutive q and b are coprime, hence `q³|Y`. Write `Y=q³*s` with `s>0`. Reducing the same expression modulo b also gives `b|Bt`, although that second conclusion is not needed below. Neither conclusion uses the first-root sign.

## Positive orientation

The exact main residual gives

```
Dstar²=U²*(1+Delta*c²).
```

We first show `Dstar>0`, before choosing a root sign. Since `c=eta+Y*k>Y*k` and `U=Y*q²`,

```
U*a*c > q²*Y²*a*k > (4*a+3)*k = H*k.
```

The middle inequality follows from `q>=3`, `Y>=1`, and `a>=2`: `q²*Y²*a >=9a>4a+3`. Expanding Dstar as

```
U*X + (U*a*c−H*k) + H*U*gamma + H*E*q + H*(R+1)
```

shows every displayed term is nonnegative and the second is strictly positive. Hence `Dstar>0`. The main square equation implies `U|Dstar`; because `U>0`, `d=Dstar/U` is a **positive** integer and

```
Dstar=U*d,             d²=1+Delta*c².
```

This uses standard integer square divisibility. The source theorem `ArithmeticAdaptiveQuotients2011.scaled_quotient` is pinned as a prospective model-level interface; no model binding or Lean application is made here.

## q⁴ divisibility

Substitution and cancellation in the exact carrier yield

```
U*(d−X−a*c−H*gamma)=H*(E*q+R+1−k).
```

Since `Y=q³*s`, `U=q⁵*s` and `E*q=X*Y*q` is divisible by q⁴. It remains to handle a possible factor 3 in H. We have

```
H=3+4*q³*s*(X+1),     gcd(H,q⁵)=gcd(3,q),
```

which divides q. Indeed, a common prime divisor of H and q divides 3. If 3 divides q, then `H≡3 (mod 9)`, so its 3-adic valuation is exactly one; if not, the gcd is one. Let `g=gcd(H,q⁵)`. The displayed balance gives `q⁵/g | E*q+R+1−k`; since `g|q`, this divisor is a multiple of q⁴. Finally `q⁴ | E*q`, so

```
q⁴ | R+1−k.
```

All divisibility here is in the ordinary integers, so the difference may be negative. No coprimality of H with q is asserted, and no cancellation of a nonunit is used.

## Remaining work and reproducibility

These deductions supply the main orientation and congruence hypotheses requested in the candidate's Cal checklist. A complete Cal proof must still classify and align the first and main Pell indices, verify every `P72Exact.indices_ordinary` input for this exact signed auxiliary valuation, and derive/bind the power-growth and projection conclusions giving `X>=q²`. Those steps are **not** established by this packet. Extending this argument to arbitrary IΣ₁ models also needs explicit model-natural quotient, divisibility and signed-root representations and checked graph evaluator bindings.

From the DiophantineConsistency directory:

```sh
python3 research/adaptive87-current-cfold-orientation-q4/check.py > /tmp/adaptive87-cfold-orientation-current.json
cmp research/adaptive87-current-cfold-orientation-q4/result.json /tmp/adaptive87-cfold-orientation-current.json
```

The finite controls exercise the inequalities, gcd identity and congruence with signed differences; they are diagnostics, not the universal proof. No Lean/build/staging was performed and no provider evidence was modified.
