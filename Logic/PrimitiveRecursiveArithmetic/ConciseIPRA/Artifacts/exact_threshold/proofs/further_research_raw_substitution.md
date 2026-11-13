# Raw variable-only substitution: focused research note

Status: an unresolved research direction, not a theorem or a claimed reduction.

## Exact question and candidate

Use the native Eq/Q/D syntax and native rules, except that full equality
transport is replaced by reflexivity and variable-source substitution:

    from x = t and u = v, infer v = u[t/x], with x a variable.

The current article proves this calculus incomplete for open sequents, even
if symmetry and formula-wide variable substitution are added. Its separating
sequent is I(0,x;u.u)=y |- x=y. The same color interpretation validates all
native theorems in the empty context, so it does not separate theorem sets.

A useful candidate closed theorem is

    Q_y (I(y,0;u.u) = 0).

The native proof applies equation induction to the constant-iteration
equation. Its usual step joins

    I(Sz,0;u.u) = I(z,0;u.u)
    I(z,0;u.u) = 0.

Neither equation supplies a variable source. This explains why the ordinary
proof does not translate directly. It is NOT a proof that no alternative
raw-variable derivation exists.

## Why the obvious naming proof is circular

On full normal forms, an existential closure packet can have the literal rows
0=0, x=t, and h(x)=r. Opening it supplies a bare variable equality x=t,
which variable substitution can use. On raw terms these rows contain selector
iterations. The computation equations relate those wrappers to their values,
but extracting x=t from a wrapped row requires a root join or conversion.
That is precisely the equality reasoning that has been deleted. Adding
normalization or backward substitution would change the problem and must be
counted as a new primitive.

## A failed finite-color construction and its exact DI obstruction

One tempting strategy gives a value a numerical component and one of three
colors: ordinary (1), defective (2), or neutral (0). Equality at the same
number relates equal colors and relates neutral to either other color.
Ordinary variables initially range over color 1. A neutral zero iteration
can be related to its seed, and an identity iterator at a positive count
can be given color 2. Then I(0,0;u.u)=0 and the successor computation relation
can hold while I(1,0;u.u)=0 fails. Flat information orders suggest ways of
making variable-to-neutral replacement preserve equations.

This does not yield a model of the entire calculus. Let

    B(x,y) := I(y,x;u.u) = x.

At a defective witness t of color 2, B(t,0) and B(t,Sz) are both true:
the zero iterate is neutral and the positive identity iterate has color 2.
But at every ordinary-color witness x, B(x,0) is true and B(x,1) is false.
Thus the DI case premise can be valid at t while no permitted variable-domain
witness makes Q_y B(x,y) true. Interpreting D by existential closure over the
variable domain makes DI unsound. Enlarging that domain to include the
defective color immediately introduces new coverage and equation-induction
obligations. No construction meeting those obligations was obtained.

This is a diagnosed failure, not evidence for a valid countermodel. In
particular, the tentative semantic operations were not presented as a fully
specified model of all term binders and substitution.

## What would count as a result

Either direction would be substantive:

1. A model or syntactic invariant sound for every remaining rule that refutes
   the displayed closed Q formula (or another closed native theorem).
2. A theorem-set equivalence proof, or a faithful public translation with
   formula round trips, that recovers the missing root joins without silently
   using conversion, arbitrary term substitution into derivations, or a new
   naming axiom.

The present note establishes neither direction.

## Source

Pinned repository: VladimirReshetnikov/ProveIt,
f25af53c682ea76c57b67c70c976bcaf836b0c91.
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/chapters/ch04_comp.tex.
Relevant labels: comp:thm:rawvsub, comp:cor:rawvsub, comp:rem:rawvsub;
question "Substitution for a variable: theorems and translations".
