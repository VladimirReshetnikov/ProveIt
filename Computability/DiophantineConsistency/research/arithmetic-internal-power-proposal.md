# Represented variable-base power and an integer perturbation bound

27 October 2026. Read-only proposal for ArithmeticInternalPower and focused
Checks. No Lean implementation, compiler, private overlay or prerequisite
refresh is performed here. ROOT requested this first checkpoint of the
half-binomial route; implementation still requires review of this exact plan.

## Fixed syntax and model scope

The only direct imports will be:

```
Foundation.FirstOrder.Arithmetic.HFS.PRF
Mathlib.Tactic.Ring
```

For arbitrary `V : Type u`, `ORingStructure V` and an actual IΣ1 model,
define `power (base exponent : V) : V` using `PR.Blueprint 1` and its
`PR.Construction`. The parameter is base, the recursion index is exponent,
the zero value is 1 and the successor is base*previous. Both blueprint
formulas are fixed before any ambient model is introduced:

```
zeroDef : Sigma1.Semisentence 2
  "out base. out=1"
succDef : Sigma1.Semisentence 4
  "out previous index base. out=base*previous"
```

The index is deliberately unused by the successor arithmetic. The accepted
result formula uses argument order output/exponent/base. Provide a fixed
public `powerDef : Sigma1.Semisentence 3` with order output/base/exponent,
using the explicit reindexing `resultDef out exponent base`; obtain
`powerDeltaDef := powerDef.graphDelta`. Prove DefinedFunction instances
via both fixed formulas and the ordinary Sigma1/Delta1 function instances.
The semantic definition is `construction.result ![base] exponent`, not an
external recursion on a standard Nat and not merely a noncomputable function
with a claimed complexity. `power_total` states unique output of the literal
public graph at all internal inputs, including zero base and exponent.

## Exact public arithmetic interface

All variables below are internal elements. Proposed names can be adjusted
without changing the endpoints. There is no global Pow instance for V; using
a named function avoids confusing internal exponents with Lean's Nat powers.

```
power_zero x : power x 0 = 1
power_succ x n : power x (n+1) = x*power x n
power_one x : power x 1 = x
one_power n : power 1 n = 1
zero_power_of_pos n (hn : 0<n) : power 0 n = 0
power_pos x n (hx : 0<x) : 0<power x n

power_add x m n : power x (m+n) = power x m*power x n
power_mul_base x y n : power (x*y) n = power x n*power y n
power_iterate x m n : power (power x m) n = power x (m*n)

power_mono_base x y n (hxy : x<=y) : power x n<=power y n
power_mono_exponent x m n (hx : 1<=x) (hmn : m<=n) :
  power x m<=power x n
power_strict_base x y n (hxy : x<y) (hn : 0<n) :
  power x n<power y n

power_two n : power 2 n = Exp.exp n
```

No positivity hypothesis is needed for monotonicity in the base; every
arithmetic-model element is nonnegative. Monotonicity in the exponent needs
base>=1: base0 has power(0,0)=1 and power(0,1)=0. Strict comparison in the
base needs exponent>0, but allows the smaller base to be 0. At exponent0
all bases give 1. Addition/product/iteration identities preserve every zero
case, including power(0,0)=1; no false multiplicative cancellation is used.

The recursion equations follow from the genuine result_zero/result_succ.
For algebraic laws, hold base parameters and the other exponent fixed before
induction on one internal exponent. Positive-base positivity follows by
successor induction. Base monotonicity uses product monotonicity. For strict
base comparison at n=t+1, weak base monotonicity plus
`x*power x t <= x*power y t < y*power y t` works even when x=0, because y>0.
For exponent monotonicity write n=m+d using the supplied order, use power_add
and `1<=power x d`. The base-two identity follows by actual exp_zero/exp_succ.

Every invariant has its real Sigma1 definability proof after the represented
function instances are installed; equality/order of total Delta1 functions
is Delta1. These are not inductions over arbitrary Lean predicates. There
is no unbounded universal over a varying base in any induction invariant.
For an implication containing order hypotheses, keep its bounded arithmetic
antecedent explicit rather than silently treating a Sigma1 implication as
closed under negation.

## Complete perturbation endpoint

The substantive arithmetic inequality included in this first pair is:

```
perturbation (a e r : V) (h : 2*r*e<=a) :
  a*power (a+e) r <= (a+2*r*e)*power a r.
```

Its proof is a genuine Sigma1 successor induction on r with the displayed
bounded antecedent. At 0 both sides are a. At r+1, the new bound gives the
old bound 2*r*e<=a. Write `a=2*r*e+d` with d>=0 by the actual arithmetic
order/decomposition theorem, or define d=a-2*r*e only after proving its
subtraction identity. The exact additive polynomial identity is

```
a*(a+2*(r+1)*e) = (a+2*r*e)*(a+e) + e*d.
```

It proves the coefficient inequality using e*d>=0. Multiply the induction
hypothesis by a+e and then use that coefficient inequality times power(a,r),
rewriting both power successors. No division, cancellation, negative term,
real inverse, or unjustified truncated subtraction enters the proof.
It retains r=0, e=0 and a=0, with only the stated bound. In particular no
positive a is smuggled into this general statement; the future ratio client
will separately have a>0 before canceling powers.

## Focused Checks and later use

Checks should expose the literal unique graph output and every public law at
arbitrary internal parameters. Include zero exponent/base identities, the
base-zero counterexample explaining the exponent-monotonicity hypothesis,
equality of distinct bases at exponent0, positive-exponent strict comparison
with lower base0, iterated powers at zero inputs, and perturbation at r0/e0
as well as its full conditional statement. Audit the public fixed graphs,
core algebraic endpoints, power_two and perturbation with standard-only axiom
reports. Finite numeral checks do not replace the internal inductions.

This pair is infrastructure plus a complete useful inequality. It does not
prove the actual Pell ratio sandwich, a binomial expansion, an odd-factorial
identity, a population bound, simultaneous source witnesses or HA equivalence.
The next separate PellHalfRatio pair can apply e=9 and the explicit finite
coefficient bounds to derive `k*N<2*c*D<k*(N+D)` from actual doubled Pell
coordinates, without a real-number oracle. Its implementation is not part
of the present request.

## Exact cache and review boundary

Reuse the accepted PellRecurrence prerequisite closure directly, not the new
BinaryPopulation main. The selected existing provider search starts at
`/tmp/arithmetic-pell-recurrence-peer-zvk0fyyh/lib`, followed only by its
explicit package/toolchain boundary paths. No shared project cache fallback
is permitted in a later fresh build. Recompute all source headers, reachable
DAG and each actual first artifact provider before freezing this inventory.

Exact scope: 95 cached custom modules, all 95 Foundation; 380 custom artifacts;
38 boundary primaries plus 76 companions, 114 total boundary artifacts;
494 first providers; zero prerequisite refresh. External package interiors
remain the inherited explicit boundary, not newly authenticated whole packages.
The original accepted receipt's historical “114 companions” wording is read
as total boundary artifacts; the counts here distinguish the two correctly.
Neither this inventory nor the existing peer cache is a newly created overlay.

Before any implementation/compiler, ROOT reviews this proposal, the complete
read-only planner and its immutable inventory/manifest. A later authorized
pair uses pinned Lean4.32 -M6000 -j1 -DElab.async=false, one thread, fresh
regular outputs and a 512MiB disk reserve. Read both complete sources and the
exact executed driver before every attempt; snapshot both sources before the
first command. Retain all failed attempts, logs, timings, commands, drivers
and available outputs. No Foundation/source refresh, shared object, Git or
shared-document mutation is included.
