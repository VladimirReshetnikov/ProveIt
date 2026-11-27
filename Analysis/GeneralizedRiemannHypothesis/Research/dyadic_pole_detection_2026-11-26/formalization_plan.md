# Lean formalization roadmap

Status: specification and dependency plan only. This archive contains no
compiled Lean proof of its new theorems. The executable Python certificate
checks algebraic identities; it does not certify analytic arguments in Lean.

## Main statements

For n : Nat, define the finite maximum

    M n z = max { norm (1 + z^(2^j)) : j < n }.

Use n >= 2 so the finite maximum has a nonempty indexing set.
For even n, L = 2^(n-1), define r as the unique real root in (1/2,1) of
r + r^L = 1. The goal is both the universal inequality

    sqrt (1-r+r^2) <= M n z

and the equality characterization

    M n z = sqrt (1-r+r^2)
       iff z = r * exp(2*pi*I/3) or z = r * exp(-2*pi*I/3).

## Finite geometry and calculus

1. Existence and uniqueness of r via continuity and strict monotonicity.
2. Squared complex norm: norm(1+w)^2 = 1 + norm(w)^2 + 2*re(w).
3. If every dyadic observation is below 1, each iterate has negative real part.
4. An absolute-angle lemma for w and w^2 both in the left half-plane:
   alpha(w^2) = pi - 2*alpha(w), where alpha(w)=abs(arg(-w)).
   Its branch conditions are indispensable; do not rewrite arg multiplicatively
   without checking the branch.
5. Solve the finite angle recurrence and use parity to obtain the weighted
   first-last identity.
6. Define g_d(u)=acos(sqrt(d)*cosh(u-log(d)/2)) on its exact closed interval.
   Verify symmetry, differentiability on the interior, and the displayed
   strictly negative second derivative.
7. Extend strict concavity to the endpoints and apply the weighted Jensen
   inequality with positive weights L/(L+1), 1/(L+1), including equality.
8. Attainment for intermediate powers uses convexity of v -> 1-v+v^2 on
   [1-r,r], where both endpoints have the same value.
9. Strong concavity of g_d supplies the explicit stability inequality.

## Three filters

The algebraic certificate is especially suitable for a separate first target.
Define tau as the unique root of t^4-2*t^2-3*t+2 on (1/2,3/5). With x=Re z,
u=norm(z)^2, define A, B, C, and P exactly as in the report. Polynomial identities
can be discharged by ring or ring_nf after substituting the quartic relation.

Analytic obligations beyond those identities are:

- Convexity of D = { (x,u) : u >= 0 and 2*x+u <= 0 }.
- Positive definiteness of Hessian(P)-2I from its first principal minor and
  determinant certificate.
- Taylor integration along line segments, proving the strong-convexity lower
  bound for P and the explicit stability estimate.

Alternatively formalize the elementary interval-feasibility proof, including
all nonnegative conditions before squaring inequalities.

## Transform application

1. Locally integrable real E of exponential order has a transform in an initial
   right half-plane.
2. Derive the forward-shift identity by changing variables. In the report's
   normalization, the symbol is 1 + (a*exp(h*(s-1)))^k, not 1+(a*exp(h*s))^k.
3. The compact-interval correction is entire. Prove the residue formula for a
   simple pole. Do not use the same residue formula without qualification for
   higher-order poles (only the leading coefficient is multiplied directly).
4. Apply the finite complex inequality to obtain the sharp residue bound.
5. The minimax lower bound is a two-point indistinguishability argument, realized
   by a real exponential oscillation with a conjugate pair of transform poles.
6. Formalize or import the classical positive-transform abscissa singularity
   lemma and deduce the filtered one-sided criterion with its real-residue sign
   hypothesis explicitly retained.

## Upstream comparison

The grh-lean repository already has the relevant abstract polar/Landau setup:
`grh/src/Lib/Analytic/Landau.lean`. An implementation could first target its
`IsPolar` interface. The proof of the new finite complex inequality itself
should depend on Mathlib rather than on the enormous arithmetic development.

No new axioms, placeholders presented as proofs, or claim of a completed
formalization is part of this roadmap.
