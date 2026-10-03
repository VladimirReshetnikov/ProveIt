# Independent review of finite-model inversion

Outcome: APPROVED, with qualifications below. This review covers the explicit inverse reversion and finite Newton hierarchy in the final integrated manuscript.

Let t=log y, choose x0 by F(x0)=t, put w=W(x0), q=g+log C, d=w/(1+w), a=d g', and write h_J=log Φ_J. For fixed J≥1, the proposed formula is

x_J(y) = x0 − q/w + B(w)/x0 + O_J((1+w)^2/x0²),

where

B = a q/w² − d q²/(2w³) − p1/w.

## Algebra and remainder

For δ0=−q/w, the order-one log residual cancels. Since F''(x0)=d/x0, g(W(x))' at x0 is a/x0, and the leading correction is p1/x0, the coefficient of x0^-1 after setting δ=δ0+B/x0 is

w B + d δ0²/2 + a δ0 + p1.

Solving gives exactly the stated B, with the displayed signs. The bounds q=O(w²), a=O(w), p1=O(w) imply δ0=O(w), B=O(w). In fact B~3w/8, a useful independent leading-order check.

Uniformly on |x−x0|≤M(1+w), one has F'''=O(x0^-2), (g∘W)''=O((1+w)/x0²), and (p1(W(x))/x)'=O((1+w)/x0²). Thus the remaining log residual is O_J((1+w)^3/x0²). The p2 term is O((1+w)^2/x0²); every higher fixed p_j term is polynomial in w divided by x0^j, hence smaller than this residual bound for sufficiently large x0. Dividing by h_J' comparable to w proves the proposed inverse remainder.

## Newton refinement

For every fixed J, h_J'=W+o(1) and h_J''=O(1/x0) uniformly on a sufficiently generous O(1+w) neighborhood of x0. The initial discrepancy h_J(x0)−t is O((1+w)^2), so the exact model inverse lies O(1+w) from x0. Choose the neighborhood with fixed margin around that localization.

For exact updates z_(r+1)=z_r−(h_J(z_r)−t)/h_J'(z_r), Taylor expansion about z_r at the root gives

|e_(r+1)| ≤ K |e_r|²/[x0(1+w)], where e_r=z_r−x_J(y).

Because e0=O(1+w), this implies, for each fixed nonnegative integer r,

|e_r|=O_(J,r)((1+w)/x0^(2^r−1)).

The first refinement is o(1+w) from the root, and induction keeps every fixed collection of iterates inside the neighborhood on which the bounds hold. This supplies the needed interval justification instead of assuming Newton convergence globally.

At y=T_n, x0=n+O(1+W(n)), so x0 and n, and their W values, are asymptotically interchangeable in these error scales. Taking 2^r−1>J+1 makes the Newton error little-o of the known forward-inversion error scale (1+W(n))^(A_J−1)/n^(J+1).

## Qualifications

- The displayed p1 correction requires J≥1; for J=0 remove its contribution.
- J and r are fixed; this statement is not a uniform result as their values increase.
- The updates use the exact limiting C and exact model values. They do not certify numerical C, finite-precision evaluation, a numerical onset, or arbitrary-target integer rounding.
- The seed x0 is the exact inverse of the leading F model. Equivalently w solves exp(w)(w²−w+1)=t and x0=w exp(w). This equation has a unique positive solution for t>1 because its w derivative is exp(w)w(w+1)>0. The Newton refinement therefore gives a finite asymptotic inverse construction relative to this well-defined leading inverse, not an elementary closed form for that seed.
- “Smaller than the forward error” should mean smaller than its stated upper-bound scale, not smaller than an unknown actual signed error.

Audit date: 2026-10-01 UTC.

## Integrated-source verification

Read the actual integrated Section 10 on 2026-10-01 at approximately 19:20 UTC. APPROVED: the source faithfully states the audited correction formula, its error, the fixed-step Newton hierarchy, and the interval argument.

Audited manuscript SHA256:

`40d52eb680316dd97f9c5c39fd208c341bc15c1c4301169da86f22d1d0751ad3`

Particular checks:

- The interval is explicitly chosen to contain the root and initial seed with margin; the uniform h' and h'' bounds and the quadratic error estimate keep the iterates inside it for sufficiently large y. This resolves the needed domain control.
- The integrated at-sequence-values sentence uses “smaller than the localization scale,” correctly referring to the stated error scale rather than an unknown actual error. With fixed J,r and 2^r−1>J+1, the ratio of the Newton upper-bound scale to the localization scale tends to zero, since v~n, omega~W(n), and any fixed power of log n is dominated by the extra inverse power of n.
- The explicit correction proposition specifies J≥1; the model constant C remains exact and no numerical certification is claimed.

No correction to the integrated source is necessary for the audited claims. PDF layout/build verification is outside this audit pass.

## Supplementary portable exact checks

`check_inverse.py` is an independent SymPy-only script, with no report imports and no file writes. Its run receipt is `check_inverse.log`. The run passed the symbolic triangular B identity, h^0/h^1 reversion residual cancellation, exact limits B/w→3/8 and delta0/w→−1/2, and eight rational derivative growth/pole checks. This supplements, rather than replaces, the analytic proof audit above.

Final artifact binding: the bibliography font-size adjustment was checked separately; it changes no mathematical content. The final source hash above includes that adjustment.
