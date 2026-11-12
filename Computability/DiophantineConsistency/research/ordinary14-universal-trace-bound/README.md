# A universal Pell-ratio trace bound and a direct-X probe

This packet proposes an external elementary lemma that removes the existing
`X>=16` hypothesis from **one trace-recovery step**. It also records a
separate 14-positive-input, 73-operation, degree-100 direct-X probe. Neither
the lemma nor the probe is a new Lean/iPRA theorem or an established
replacement equation. In particular, recovering `X=2^R` does **not** by
itself recover the `q|X` needed to map the probe back to the reviewed
[`14/74` parent](../ordinary14-positive-guard74/). The derivation, exact
graph and finite checks require independent review.

## Precise lemma

Let X,Y,N be positive integers with `R=2N+1`, and set

```
a=Y*(X+1),  A=a+2,  m=X*Y²,  P=2m+1,  H=4a+3,
c=psi_A(R),  k=2*psi_P(N+1),  d=chi_A(R).
```

Here `(p+sqrt(p²−1))^j=chi_p(j)+psi_p(j)*sqrt(p²−1)`.
Assume the **Pell-ratio interval**

```
Y*k < c < (Y+1)*k.                                      (1)
```

In the maintained construction (1) follows from positive eta,zeta and
`c=eta+Y*k`, `k=eta+zeta`; the lemma does not derive the exact indices or
that interval from a graph zero. Then

```
2^(R−2) <= Y,     0 < 2^R <= 4Y < H,     0 < X < H.   (2)
```

Consequently, if in addition `d≡X+a*c (mod H)`, the standard trace identity
`d=2^R+a*c+H*z` gives `X≡2^R (mod H)`; both are in `[0,H)`, so
`X=2^R`. This inference uses an **unscaled** congruence. It cannot cancel a
factor 3 from a congruence modulo H without separate justification.

## Elementary ratio proof

For p>=2 and j>=1, the Pell norm and recurrence imply

```
(2p−1)^(j−1) <= psi_p(j) <= (2p)^(j−1).
```

Indeed, the norm gives `(p−1)*psi_p(j)<chi_p(j)<=p*psi_p(j)`;
the upper inequality uses `psi_p(j)>=1`. Insert these in the recurrence
`psi_p(j+1)=chi_p(j)+p*psi_p(j)` and induct from `psi_p(1)=1`.

Define

```
L=(2A−1)²/(2P),  B0=(X+1)²/X.
```

The lower c bound and upper k bound give `c/k >= L^N/2`. Exact expansion
gives

```
X*(2A−1)² − (X+1)²*(2P)
  = 12*X*Y*(X+1)+9*X−2*(X+1)² > 0,
```

where positivity follows already from X,Y>=1. Thus `L>B0>=4`, the latter
by `(X−1)²>=0`. Because N>=1,

```
c/k > 4^N/2 = 2^(R−2).
```

By the upper half of (1), `Y+1 > 2^(R−2)`. Both Y and
`2^(R−2)` are integers, so `Y>=2^(R−2)`, proving (2). The standard
`projection_quotient` theorem in the pinned
`ArithmeticPellPowerRecovery.lean` states the cited trace identity. The
earlier `power_bound` theorem there assumes `X>=16` to prove the stronger
`2^R<Y`; this packet needs only `2^R<H` and does not claim that stronger
bound for small X.

## The 73-gate direct-X graph and the remaining gap

The [candidate graph](candidate.json) deletes the `X=q*w` row of the 74-parent
and replaces positive input w by positive input X. It has 73 live gates,
14 positive inputs and four fixed leaves. At signed assignments related by
`X=q*w`, it evaluates identically to the parent. At fixed ports,
`deg(F0)<=20`, `deg(F1)<=28`, `deg(Fa)<=28`, `deg(Fs)<=22` and
`deg(guard)<=2`, so the product output has degree at most 100. A nonuniform
ray at the authenticated ports modulo 1,000,000,007 has degree 100 and
leading coefficient 459525008, proving exact specialized degree 100.

For a putative positive probe zero, the four restricted unit factors force
the guard factor to 1. Thus `Bprime=b*(h−1)>=0`. Even when `h=1`,
positive F and `X+K0>0` force `C>0`; the existing scalar rank window and
fact-level index replay may then be investigated **without assuming a
parent zero**. If they establish the lemma's exact indices and interval, the
modified main carrier supplies the unscaled trace congruence, and the lemma
recovers `X=2^R`. The parent map still needs **q|X** to reconstruct positive
w. The old `q|3X` proof used the `E*q` term that was absorbed into the
modified carrier; it cannot be borrowed from the old literal-zero wrapper.

The checker provides a finite **toy control**, not a full graph zero: set
`q=3`, `N=17`, `R=35`, `X=2^R`, and

```
Y=(1/2)*sum_{j=0}^N binom(2N,j)*X^(N−j).
```

It verifies `q³|Y`, `R+1<q⁴`, the first and main Pell norms, the exact
indices/ratio interval and the unscaled trace congruence, yet `q∤X`. Its
Y has 595 bits and SHA-256 (little endian)
`f4a97f4b243ae8b62c6c163f151e00aca018af63dd828955e94bae6cffc2751c`.
This q is not the authenticated compact44 q, and the control does not
check all graph residuals, the rank/guard equations or a parent witness.
It shows only that the displayed Pell/trace facts alone do not imply q|X.

## Checks and limitations

The checker pins the relevant Lean source statements and graph bytes, checks
the source delta/topology/liveness and 100 signed parent substitutions,
authenticates the ports, verifies the degree ray, checks 5,880 finite Pell
recurrence instances and the toy control. Finite checks do not replace the
unbounded ratio argument or establish any modified-graph provider closure.
The bounds, graph and source-hypothesis tracing are submitted for independent
review; no Lean run or internal iPRA theorem is claimed.

```
python3 -I -S -B research/ordinary14-universal-trace-bound/check.py > /tmp/universal-trace-bound.json
cmp /tmp/universal-trace-bound.json research/ordinary14-universal-trace-bound/result.json
```

Independent source review is recorded in
`../../reviews/ordinary14-universal-trace-bound-independent/`.
