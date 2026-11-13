# Membership-only elimination majors: an exact obstruction

Pinned comparison: ProveIt `2fa4637b3bf922beea0052a5210c22b14482950b`.

## Mathematical calculus under test

Start with the native scalar calculus with terms `x,0,S(t),I(n,a;u.h)`.
Keep its two computation equations, hypotheses, the two D introductions,
and its transport, Q elimination and D elimination. Modify each elimination
so that its major is required to be literally a member of the current
assumption context, rather than merely derivable. Permit adding any
computation equation to the context; this is stronger than having only the
computation axioms as leaves and matches the compact protocol's useful
administrative extension. The ordinary minor/continuation derivations remain
unrestricted within this modified calculus. Call it M.

The same argument applies to the guarded root-selected introduction, since
every introduction still concludes a D formula.

## Proposition

With an open numerical parameter `v`, the native calculus proves

    I(v,0;u.u) = 0,

but M does not prove it from the empty assumption context. Thus replacing
all recursively verified majors by context membership cannot preserve all
open native consequences.

## Native proof

Let `E(y)` be `I(y,0;u.u)=0`. Zero computation proves `E(0)`.
From `E(z)`, successor computation and equality give `E(S z)`.
Equation induction gives `E(v)`. In the paired-D formulation, introduce
`D_{x,y} E(y)` by progress, eliminate it at a fresh unused `b` to obtain
`Q_y E(y)` in context, and apply Q elimination to the proved base `E(0)`
at target `v`. This explicitly uses a *derived* D major.

## Why the modified proof cannot use induction

Consider a derivation whose goal is an equation and whose assumptions are
equations only. A D introduction cannot be its last substantive step,
because its conclusion is compound. A Q elimination cannot occur, because
its major would have to be a Q formula in the equation-only context.
A D elimination cannot occur for the same reason. Computation appends an
equation, preserving the context invariant. Transport along a retained
equation, when its conclusion is an equation, has an equation as its minor
premise: substituting numerical terms never changes the root constructor of
a formula template. Its continuation has the original equation goal and
an equation-only context. Hypothesis is harmless.

Induction on a putative finite derivation therefore erases every logical
possibility and leaves a derivation using only hypotheses, computation
equations and equality transport. In the raw checker presentation, scalar
neutral context entries can also be allowed: they decode to the true
equation `0=0` and do not supply a Q or D major.

## Equational countermodel

Use the free term algebra with the numerical parameter `v`, quotiented by
the two iterator computation equations. Equivalently, use their full normal
forms. The repository's full-normalization development proves termination,
confluence and substitution coherence; the algebra validates both
computation equations and all equality transport. The term
`I(v,0;u.u)` is a neutral iterator in full normal form, distinct from the
normal form `0`. Hence the displayed equation is false in this algebra.
The equational derivation just described cannot exist.

## Precise scope

This is a separator for **open native consequence**, not a new claimed
closed public-goal counterexample for every possible re-encoding. A redesign
could still prove a suitable closed encoding by different introduction
rules. Such a redesign would need a new theorem-completeness proof; the
existing native equivalence cannot simply be reused.

The repository already handles a different, sound forward optimization:
`retained_premises` keeps recursive verification of the minor premise and
retains the derived target for its continuation. It does not globally
replace all major verification by membership. Its treatment and the
global-floor delayed-export issue are in Chapter 11, subsection
`Retained majors`.

## Standard focused repair and its cost

The focused repair is to add equation induction directly:

    Gamma |- E(0),    Gamma,E(z) |- E(S z)
    ------------------------------------
                  Gamma |- E(t)

with `z` fresh and `E` literally an equation. This is equivalent to the
native progressive introduction plus D elimination and Q elimination.
It prevents the obstruction above, but it adds a genuine recursively
verified subderivation (and a supplied template/target or an equivalent
reconstruction). It is not a justification for simply deleting the old
recursive major call. No smaller complete checker is claimed here.
