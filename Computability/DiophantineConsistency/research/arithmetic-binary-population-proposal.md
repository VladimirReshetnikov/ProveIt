# Represented binary population in internal arithmetic

Proposed on 27 October 2026. This is a new internal arithmetic package,
not an application of an external finite array at a nonstandard length.
ROOT will author ArithmeticBinaryPopulation and focused Checks. The only
imports are Foundation.FirstOrder.Arithmetic.HFS.PRF and Mathlib.Tactic.Ring.
Their exact cached closure is already the accepted PellRecurrence closure:
95 Foundation modules, 380 custom artifacts and 38 external names with
114 boundary artifacts, for 494 selected providers and zero refreshes.
A new read-only inventory must reauthenticate that complete DAG and every
actual first provider before a compiler or private overlay is created.

## Actual total represented functions

Use Foundation's bounded binary digit fbit(a,i), including its actual
zero-above-length behavior. Define a primitive recursive prefix:

```
prefix(0,a) = 0
prefix(n+1,a) = prefix(n,a) + fbit(a,n)
population(a) = prefix(length(a),a).
```

PR.Blueprint and PR.Construction supply fixed Sigma1 and Delta1 graphs
and unique total values for every internal a,n in every IΣ1 model. Give
an explicit formula for population's composition with the represented
length graph. Do not infer formula complexity from Classical.choose or
from an external function. No externally finite summation is the definition.

Prove prefix(0,a)=0, its successor identity, prefix(n,0)=0,
prefix(n,a)<=n, and stabilization at any n>=length(a). These are genuine
definable successor inductions with Foundation's fbit_le_one and
fbit_eq_zero_of_le; no assumption on standardness is allowed.

## Complete binary and block endpoints

Prove, for arbitrary internal a,n:

```
prefix(n+1,2*a)   = prefix(n,a)
prefix(n+1,2*a+1) = prefix(n,a)+1
population(0) = 0
population(2*a) = population(a)
population(2*a+1) = population(a)+1
population(a) <= length(a) <= a.
```

The prefix shift is an induction on n using the already proved actual
fbit shifts; it is valid even at a=0. Use the precise length identities,
splitting the zero case only for the even length formula.

The substantive arbitrary-length block endpoints are:

```
b < Exp.exp n ->
  population(A*Exp.exp n+b) = population(A)+population(b)

a < Exp.exp n ->
  population(a)+population(Exp.exp n-1-a) = n.
```

For concatenation, fix A and induct on n with the bounded formula
forall b<exp(n), the displayed equality. Decompose b=2*(b/2)+b%2,
where b%2 is zero or one. From b<2*exp(n) derive b/2<exp(n), apply
the induction hypothesis, and use the actual even/odd recurrences for
both the concatenated number and b. This includes A=0,n=0,b=0.

For complement, induct on n with the bounded formula forall a<exp(n).
Write a=2*q+r with r=0 or1 and q<exp(n). Derive before rewriting

```
Exp.exp(n+1)-1-a = 2*(Exp.exp n-1-q)+(1-r).
```

All subtractions are justified by q<exp(n) and a<exp(n+1). The low
bits r and1-r add to one; the induction hypothesis gives n for the
remaining blocks. This proves the exact complement weight without an
external finite set or a supplied population equation.

Conclude population(Exp.exp n)=1 and population(Exp.exp n-1)=n.
The first follows by induction from the even recurrence; the second is
the complement endpoint at a=0. These are the exact internal counterparts
of the external binary scale, concatenation and complement lemmas used
in the mask/rank population argument. No central-binomial, carry-free or
mask property is assumed in their statements.

## Review and execution boundary

Every induction over internal values must have an actual Sigma1
definability proof, with bounded quantified inputs when needed. The
fixed graph instances must cover all functions appearing in that proof.
The complete main, Checks and exact executed driver must be read before
the first command. Snapshot both inputs before compiling the main.
Use pinned Lean4.32, -M6000 -j1 -DElab.async=false, one thread, private
fresh regular outputs and a 512MiB reserve. Preserve every attempt,
including failed elaboration, complete logs, times, commands and drivers.
Independently review and replay both final leaves; compare both objects,
complete logs and every standard-only axiom report before acceptance.

## Obligations this package does not discharge

Population subadditivity, its exact carry defect and zero-carry
characterization, internally encoded variable-length words, fixed mask
weights, binomial valuations and the internal half-binomial estimate
remain. In particular the external real-number Pell ratio estimate is
not an internal theorem. Simultaneous converse witnesses, tableau
soundness, source-ZFC calibration and final HA proof existence remain.
The displayed equation and all metric frontiers are unchanged.
