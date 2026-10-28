# Internal population subadditivity and the exact no-carry test

Read-only mathematical proposal, 27 October 2026. No Lean source, compiler,
overlay or prerequisite refresh is proposed for execution yet. ROOT's
ArithmeticBinaryPopulation pair is still undergoing its author build.
Its eventual independently accepted provider must be selected before the
new cache inventory is frozen. No provisional population object is used.

## One substantive next pair

Proposed `ArithmeticBinaryCarry` and focused Checks, with the sole import
`DiophantineConsistency.ArithmeticBinaryPopulation`.
Work in every arbitrary internal IΣ1 model, using that parent's actual
represented population function and Foundation's bounded `fbit`.
The complete public targets are:

```
population(a+1) <= population(a)+1
population(a+b) <= population(a)+population(b)
population(a+b) = population(a)+population(b) <-> NoCarry(a,b)
```

NoCarry is a fixed bounded arithmetic predicate:

```
NoCarry(a,b) := forall i <= a+b, fbit(a,i)+fbit(b,i) <= 1.
```

Expose its literal Sigma0 graph and all-index meaning, and derive the
strict-defect counterpart when NoCarry fails. No external finite array,
assumed carry equation, standard-index premise, population oracle,
2-adic valuation or binomial theorem is needed. This is an actual equality
characterization; the theorem does not stop at a sufficient disjointness
condition.

## Fixed syntax and all-index bit meaning

Use a fixed `noCarryDef : Sigma0.Semisentence 2`, for example

```
a b. forall i < a+b+1,
  exists u < 2, exists v < 2,
    fbitDef(u,a,i) and fbitDef(v,b,i) and u+v <= 1.
```

The actual `fbit_defined`, `fbit_lt_two` and uniqueness of the fixed graph
give exact evaluation iff NoCarry. This formula is independent of the
ambient model. Bounded outputs do not require a new represented recursion.

Prove the pointwise equivalence

```
NoCarry(a,b) <-> forall i, fbit(a,i)+fbit(b,i) <= 1.
```

For i>a+b, both digits vanish: length(a)<=a<=a+b<i and the analogous
bound for b imply `fbit_eq_zero_of_le`. The reverse implication simply
restricts the index. The unbounded statement is a useful theorem only;
the induction motive uses the original bounded Sigma0 predicate.
The sum-zero case is included: a=b=0 and the sole bounded test i=0 passes.

Next prove, for internal a,b,r,s with r<=1 and s<=1,

```
NoCarry(2*a+r,2*b+s) <-> r+s<=1 and NoCarry(a,b).
```

At index zero the actual fbit values are r and s. At index j+1 they are
the bits of a and b at j. Establish these two generic bit identities by
the actual r=0/1 and s=0/1 alternatives, using the parent's Foundation
even/odd fbit lemmas. For arbitrary i, split i=0 or i>0; in the second
case use j=i-1 and the justified j+1=i. This is a local arithmetic case
split, not induction over external Nat. The all-index equivalence above
avoids an invalid attempt to compare two unequal finite bit bounds at
the zero case. No positivity of a+b is a premise of the binary recursion.

## Successor bound by genuine internal order induction

Let a=2*u+r, where u=a/2 and r=a%2. Actual `div_add_mod`, `mod_lt`, and
`le_one_iff_eq_zero_or_one` justify this decomposition.

The motive is `population(a+1)<=population(a)+1`, which is Delta1/Sigma1
because the parent represents population as a total function. Apply the
actual internal Sigma1 order induction. At a=0, population(1)=1 and
population(0)=0. At a>0, `div_lt_of_pos_of_one_lt` gives u<a.

- If r=0, the two binary recurrences give
  population(a+1)=population(u)+1=population(a)+1 directly.
- If r=1, population(a+1)=population(u+1). The induction hypothesis
  gives this <=population(u)+1=population(a), and hence it is strictly
  below population(a)+1.

The second branch is stronger than the public bound; retain it as a
local lemma if useful. There is no assumption that the successor has
only one binary carry.

## Simultaneous subadditivity and exact equality

Use order induction on the internal sum N, with the genuinely bounded
formula

```
forall a<=N, forall b<=N, a+b=N ->
  (population(a+b)<=population(a)+population(b) and
   (population(a+b)=population(a)+population(b) <-> NoCarry(a,b))).
```

All quantifier bounds are arithmetic terms. The equality of represented
population values is Delta1; the NoCarry predicate is Sigma0, so the
conjunction and biconditional have a Sigma1 representation. Use the
parent's graphDelta or the actual total-function hierarchy conversion
if an explicit definability instance is needed. Do not use an unbounded
forall a,b induction motive and do not infer definability from a chosen
semantic function.

At N=0, nonnegativity forces a=b=0. For N>0 put

```
A=a/2, B=b/2, r=a%2, s=b%2, H=A+B.
a+b=2*H+(r+s).
```

Derive H<N before invoking the induction hypothesis: if H=0 the result
is immediate from N>0; if H>0 then H<2H<=N. Also A<=H and B<=H.
Thus the induction hypothesis at H applies to the exact pair A,B.
Split the four actual remainder alternatives; equivalently group them
according to whether r+s<=1 or r=s=1.

If r+s<=1, the parent's binary recurrences give

```
population(a+b) = population(H)+(r+s),
population(a)+population(b) = population(A)+population(B)+(r+s).
```

Add the common low-bit contribution to the induction inequality. Addition
cancellation reduces equality to the induction equality at A,B. The
NoCarry binary recursion reduces its right side to the same condition,
since the low bits already sum to at most one. This proves both directions
of the equality characterization in all three nonoverlapping low-bit cases.

If r=s=1, the actual sum is 2*(H+1), and

```
population(a+b) = population(H+1)
              <= population(H)+1
              <= population(A)+population(B)+1
               < population(A)+population(B)+2
               = population(a)+population(b).
```

The first inequality is the separately proved successor bound, not an
assumed no-carry property. Hence equality is impossible even if higher
carries propagate. NoCarry is also false because its actual index-zero
test has value 1+1>1. This establishes the inequality and both directions
of the biconditional without subtracting an unjustified defect.

Finally instantiate the bounded motive at N=a+b. By linear order and the
proved inequality, derive

```
population(a+b)<population(a)+population(b) <-> not NoCarry(a,b).
```

These conclusions include a=0, b=0, a=b=0 and arbitrary nonstandard indices.
Useful focused checks should include the zero cases, a=b=1 (strict defect),
the generic low-bit overlap obstruction, and direct extraction of every
internal fbit inequality from a population equality. There is no need to
enumerate a large standard interval.

## Existing exact API and pending inventory boundary

Foundation Exponential/Log supplies `fbit_defined`, `fbit_lt_two`,
`fbit_le_one`, `fbit_eq_zero_of_le`, `fbit_zero`, both successor-bit shifts,
both zero-position bit identities and `length_le`. IOpen/Basic supplies
`div_add_mod`, `mod_lt`, `div_lt_of_pos_of_one_lt` and the actual represented
division/remainder graphs. PeanoMinus/Basic supplies the zero/one
alternative from a bound by one and justified predecessor arithmetic.
No new Foundation import is needed beyond the proposed parent.

The expected reuse after parent acceptance is its exact 95 Foundation
modules/380 artifacts and 38 boundaries/114 total boundary artifacts,
plus the newly accepted Population main object: 96 custom modules,
95 Foundation modules,381 custom artifacts,495 first providers,zero
refresh. These are prospective counts, not an authenticated new inventory.
The eventual audit must select the exact accepted parent source/object,
recompute the sole-import reachable DAG, check all existing source and
artifact pins and actual first providers, and preserve the parent's
author/independent histories. No parent Checks object is an import.

This proposal intentionally does not freeze an inventory while Population
is provisional. After ROOT reviews the mathematics and its accepted
provider is available, prepare the exact read-only inventory before any
new Lean source/compiler/overlay authorization.

## Remaining proof work

The equality test is the internal binary no-overlap fact used in masked
population arguments. It does not alone interpret an arbitrary internal
word, establish fixed-mask weights, recover a digit/carry tableau or
connect the main Pell quotient to population. Binomial valuations,
half-binomial estimates, simultaneous witness construction and the final
HA equivalence remain separate. This is neither a supplied-word theorem
nor a claim that the whole polynomial soundness argument is finished.
