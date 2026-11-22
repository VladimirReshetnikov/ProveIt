# Route from the checked rational kernel to object iPRA

## Verification levels

1. `Truncation.lean`, `Energy.lean`, `Examples.lean` and `Audit.lean` are compiled
   host Lean proofs, with the axiom dependencies disclosed in the README.
2. The source audit establishes that the repository contains explicit
   `Prf PRAAx` proofs for finite weighted sums, common denominators, signed
   parts, Cauchy–Schwarz, common-envelope truncation and conditional-average
   regrouping. Those repository libraries were **inspected, not rebuilt here**.
3. The new excess-tail inequality, completion, quantitative Vitali producer
   and density construction are not yet newly reified in `Prf PRAAx`.
   Their specific remaining obligations follow.

The target syntax is `LeanProofs.ConciseIPRA.PTm`, with formulas `Fm PTm n`,
axioms `PRAAx`, and the intuitionistic judgment `Prf PRAAx Γ φ`, written
`Γ ⊢[PRAAx] φ`. `PR k` is syntax for primitive recursive functions of fixed
arity, not a universal evaluator. The actual quantifier-free induction API is

```lean
PRA.qfInd (φ : Fm PTm (n + 1)) (hφ : φ.QF)
  (h0 : Γ ⊢[PRAAx] φ.subst (inst zero))
  (hS : φ :: Γ.map Fm.shift ⊢[PRAAx]
    φ.subst (repl (succ (var 0)))) : Γ ⊢[PRAAx] Fm.all φ
```

For each fixed finite presentation algorithm, give PR symbols for its step
index, list length, cell numerator, denominator, refinement map and all
moduli. Uniformly executing a variable number of independently total program
codes does not follow. Such a case instead needs one fixed PR batch producer,
a supplied clocked table, or an explicit relational trace hypothesis.

## 1. Signed rational and step-table coding

Represent a rational by `(p,n,d)` with value `(p-n)/(d+1)`. Never decide equality
or sign of a completed real. All finite comparisons clear positive natural
number denominators. A step function is a finite table over a common dyadic
partition. Its length, dimension, denominator and entries are natural codes.
Refinement repeats the appropriate entries; cell weights are rational and
nonnegative. Use a product of the finitely many positive denominators as a
uniform common denominator; this is primitive recursive, without a hidden
least-common-multiple minimization.

`SignedParts.part_identities` already gives the natural-number presentation
of positive part, negative part and absolute value. `TowerCommonDen.common_den`
already proves the common-denominator correctness equation. `FiniteKernel`
records that cross-multiplied expectation comparisons are quantifier-free.

## 2. Stable clipping and excess

At common denominator D, let `X` and `Y` be signed integers, let K be the
integer clipping threshold in those units, and let `A=|X-Y|`. Define

* `rhoNumer = min(D,A)`;
* `excessNumer(K,X) = max(|X|-K,0)`;
* `clipNumer` by the three rationally decidable regions `X<-K`, `-K≤X≤K`,
  `K<X`.

Here the real clipping level is `K/D`; the hypothesis `K/D ≥ 1` is the
quantifier-free inequality `D ≤ K`. The pointwise stable inequality becomes

```
D |X-Y| ≤ 2 K min(D,|X-Y|)
             + D excessNumer(K,X) + D excessNumer(K,Y).
```

Its proof has finitely many order cases, each a semiring inequality after
clearing signs. No real-valued indicator must be evaluated. Establish the
three clipping regions once, then use the existing integer-pair ring and
order-certificate mechanisms. The square estimate becomes

```
4 K excessNumer(K,X) ≤ X².
```

On the `|X|>K` branch its slack is `(|X|-2K)²`; on the other branch the
left side is zero. This is an explicit nonnegative polynomial certificate.

## 3. Variable-length integration

Let `w(i,z)` be the nonnegative natural weight body, and let `A(i,z)` and
`B(i,z)` be the two sides of the cleared pointwise inequality. The invariant
at prefix length J is

```
sum_{i<J} w(i,z) A(i,z) ≤ sum_{i<J} w(i,z) B(i,z).
```

The loop guard `J≤N` and this inequality are quantifier-free after replacing
bounded sums by their PR symbols. The base is `0≤0`. The step adds the local
pointwise inequality at J. Use `Core/Sums` and the actual `PRA.qfInd` API,
then specialize J to N. This proves one variable-length theorem; do not
replace it by a schema enumerating every fixed numeral length.

The existing `Expectation.exp_mono` already implements this kind of sum
lifting. Use `Expectation.exp_add` and its scalar identities to regroup the
right side. The resulting invariant for the stable inequality is

```
D S_distance(J) ≤ 2 K S_rho(J) + D S_excessX(J) + D S_excessY(J).
```

## 4. Uniform integrability and names

An L1-name is a **fixed PR step-table producer** plus a proved quantitative
Cauchy contract, not an arbitrary host function `Nat → Rat`. Express that
contract as a first-order formula universally quantifying numerical precision
and pair indices. To show that the producer built from a convergence-in-measure
name is L1 Cauchy, instantiate the stable finite inequality at the selected
K and two selected table levels, then insert the two tail bounds and the
`rho` bound. The elementary rational error allocation is a separate finite
order derivation.

If a family has L2 bound C, the excess estimate gives the tail bound
`C/(4K)`. Choose a positive integer K by an explicit rational ceiling. The
search for K is not open-ended. A supplied PR modulus for the `rho`-Cauchy
contract then yields a PR L1 modulus by composition. The completion theorem
constructs its output table sequence by a fixed precision substitution.

The full output contract is an open formula with all required producer
hypotheses. `Prf.subst` specializes programs and parameters; `Prf.trans`
discharges exactly those hypotheses with available object derivations.
An ordinary Lean proof of that contract is not a replacement for this step.

## 5. Conditional averages and energy

For two child rational numerators a,b, the denominator-cleared energy
identity is

```
2(a²+b²) = (a+b)² + (a-b)².
```

This is a fixed polynomial identity handled by the repository's existing
ring-to-derivation mechanism. The general finite orthogonality proof groups
fine cells by a coarse cell. The equation defining the average cancels the
cross term on each coarse cell; `TowerCommonDen.regroup` supplies precisely
the required change in order of finite sums. The weighted identity is

```
sum w(f-g)² = sum wf² - sum wg²
```

provided `sum wfg = sum wg²`. `Energy.finite_orthogonal_energy` checks this
algebraic reduction in host Lean. The conditional-average producer and the
finite proof of its orthogonality equation remain object-level work.

For an energy-tail modulus R, the invariant at refinement stage m is the
sum of squared sibling details between the base level and m. Telescoping
identifies it with the energy difference. The tail bound provides the L2
Cauchy contract; `Expectation.cauchy_schwarz` then supplies L1 control on a
probability space. The construction never infers a tail modulus merely from
bounded monotone energy.

## 6. Metastability without a convergence modulus

Fix a PR window function g and define endpoints by a fixed recursion
`N(0)=0`, `N(j+1)=N(j)+g(N(j))` (or a strict version if positive window length
is desired). At a common rational denominator, the failed-search invariant is

```
E(N(j)) ≥ E(N(0)) + j δ.
```

This is quantifier-free and has the direct one-step proof given by the failed
comparison at j. Choose a natural bound T with `T δ>B`. Bounded search over
`j<T` must return a comparison `E(N(j+1))≤E(N(j))+δ`, because failure would
contradict the energy cap. `Energy.smallWindow` is that executable search;
`energy_window` is its checked host proof. A PR-coded g is fixed before this
argument is compiled. A numerical code for an arbitrary total g is not
silently used as an evaluation oracle.

This produces a finite stable window. It does not construct one index after
which every future term is close. That stronger conclusion needs the
separately supplied energy-tail modulus.
