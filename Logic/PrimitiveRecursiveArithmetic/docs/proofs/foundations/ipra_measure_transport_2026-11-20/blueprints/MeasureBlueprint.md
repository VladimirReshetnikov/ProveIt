# Measure-theory formalization blueprint

This file specifies definitions and proof tasks for the measure section.
It is a blueprint, not a claim that the completion theorems have been
elaborated in Lean. The separate checked scalar modules are the
authoritative record of completed host Lean lemmas.

## 1. Host data and the object-language boundary

The convenient host definitions below use Rat, arrays, and functions.
A host function Nat → Step is not automatically primitive recursive.
The object implementation must provide a fixed PRCode, its bounded
execution trace, and an actual iPRA proof for each advertised finite contract.
Quantification over arbitrary producers in a host theorem is a metatheorem
about a family of object proofs.

~~~lean
structure Step where
  level : Nat
  values : Array Rat
  length_eq : values.size = 2 ^ level

-- Refine by repeating each entry 2^(newLevel - level) times.
def refine (a : Step) (newLevel : Nat) (h : a.level ≤ newLevel) : Step := ...
def mapStep (f : Rat → Rat) (a : Step) : Step := ...
def zipOnCommonRefinement (f : Rat → Rat → Rat) (a b : Step) : Step := ...
def sumValues (a : Step) : Rat := a.values.foldl (· + ·) 0
def integral (a : Step) : Rat := sumValues a / (2 ^ a.level : Rat)
def norm1 (a : Step) : Rat := integral (mapStep Rat.abs a)
def energy (a : Step) : Rat := integral (mapStep (fun x => x * x) a)
def subStep (a b : Step) : Step := zipOnCommonRefinement (· - ·) a b
def distance (a b : Step) : Rat := norm1 (subStep a b)
def dyadic (p : Nat) : Rat := 1 / (2 ^ p : Rat)

structure L1Name where
  approximant : Nat → Step
  regular : ∀ p q, p ≤ q →
    distance (approximant p) (approximant q) ≤ dyadic p

structure L1Equivalence (f g : L1Name) where
  demand : Nat → Nat
  close : ∀ k p q, demand k ≤ p → demand k ≤ q →
    distance (f.approximant p) (g.approximant q) ≤ dyadic k
~~~

The ellipses identify implementation tasks; they are not proofs.
The complete mathematical definitions are the algorithms in the report and
in measure_demo.py. Initially retain names and equivalence witnesses rather
than quotienting them. Transitivity of L1Equivalence uses the maximum of the
two demands at precision k+1.

## 2. Finite foundational lemmas

Implement in this order:

1. refine_length, refine_refine, integral_refine, norm1_refine,
   energy_refine.
2. Exact linearity, positivity, abs_integral_le_norm1, triangle inequality,
   and norm1_sub_norm1_le.
3. The denominator-cleared Cauchy--Schwarz identity:
   J*sum(u_i²) - sum(u_i)² = sum_{i<j}(u_i-u_j)².
4. norm1_sq_le_energy, with positive denominator proofs explicit.
5. Coordinatewise Lipschitz lifting as one reusable finite weighted-sum lemma.

The object proof of each sum lemma is quantifier-free induction on the
number of processed cells. Double sums and refinement use nested bounded
loops. There is no induction on an infinite-convergence predicate.

## 3. Stable Vitali data

Reuse the checked definitions clip, excess, and rho from the scalar
module when integrating this blueprint.

~~~lean
def d0 (a b : Step) : Rat :=
  integral (zipOnCommonRefinement rho a b)
def excessIntegral (K : Rat) (a : Step) : Rat :=
  integral (mapStep (excess K) a)

structure VitaliData where
  seq : Nat → Step
  measureRate : Nat → Nat
  tailCutoff : Nat → Rat
  cutoff_ge_one : ∀ p, 1 ≤ tailCutoff p
  measure_cauchy : ∀ q m n,
    measureRate q ≤ m → measureRate q ≤ n →
    d0 (seq m) (seq n) ≤ dyadic q
  uniform_tail : ∀ p n,
    excessIntegral (tailCutoff p) (seq n) ≤ dyadic p
~~~

For K≥1, ceilLog2Rat K is a bounded search for the first h satisfying
K≤2^h. A concrete scan bound is max 1 (K.num.natAbs+1), which dominates the
required exponent because a rational denominator is positive. A bit-length
implementation is preferable after proving its correctness.

Set M(p)=measureRate(p+3+ceilLog2Rat(tailCutoff(p+2))) and
Mhat(p)=max_{j≤p}M(j).

Targets:

- vitali_pair_bound: for m,n≥M(p), distance(seq m,seq n)≤(3/4)2^(−p).
- vitali_name: return an L1Name with approximant seq(Mhat(p)).
- vitali_converges: the original sequence is within 2^(−p) of that name
  after M(p+1), stated first as finite comparisons with every sufficiently
  late approximant.
- l2_tail_producer: derive uniform_tail from finite energy≤C by integrating
  4K*excess(K,x)≤x².
- envelope_tail_producer: take the maximum absolute entry in a strong
  envelope's (p+1)-st approximant. Its error controls the excess integral.
  Avoid sharp event predicates on the completed envelope.

The finite clipping and excess-square inequalities already have checked
host implementations. Construction of L1Name, encoded primitive recursive
schedules, and internal Prf PRAAx versions remain distinct obligations.

## 4. Rectangles, partial averages, and the tower

A RectangleStep has two levels and an array of length
2^xLevel * 2^yLevel; flatten (i,j) as i*2^yLevel+j. Include explicit row
and column bounds. Define total, row, and column averages and their
absolute-value versions.

Targets:

- row_average_contraction.
- finite_fubini: equality of total and both iterated averages.
- partial_average_name: apply the contraction to each approximant; its
  exact rapid rate is preserved without guard bits.
- conditionalAverage(n): block average when n≤level; refinement otherwise.
- conditionalAverage_integral, _positive, _contraction, _tower.
- conditionalAverage_rate: if n≥level(f.approximant(p+1)), the two errors
  from replacing f by that finite step sum to at most 2^(−p).

Fubini concerns completed averaging operators. Identification with
almost-everywhere classical section integration is a separate semantic
comparison, not an internal assumption.

## 5. Dyadic masses and density construction

~~~lean
structure DyadicMasses where
  value : (n : Nat) → Fin (2 ^ n) → Rat
  nonneg : ∀ n i, 0 ≤ value n i
  -- leftChild and rightChild include explicit Fin bounds.
  coherent : ∀ n i,
    value n i =
      value (n+1) (leftChild i) + value (n+1) (rightChild i)

def densityStep (v : DyadicMasses) (n : Nat) : Step := ...
def massEnergy (v : DyadicMasses) (n : Nat) : Rat :=
  energy (densityStep v n)

structure EnergyRate (v : DyadicMasses) where
  rate : Nat → Nat
  tail : ∀ p n m, rate p ≤ n → n ≤ m →
    massEnergy v m - massEnergy v n ≤ dyadic p * dyadic p
~~~

Targets:

1. conditionalAverage_density, by repeated mass coherence.
2. cross_energy: average(d_m*d_n)=H_n for m≥n.
3. density_energy_difference: energy(d_m-d_n)=H_m-H_n.
4. density_l1_sq_bound, by finite Cauchy--Schwarz.
5. density_name: r(p)=max(p,max_{j≤p}rate(j)) is increasing, cofinal,
   and produces a strong name.
6. density_represents_cell, then finite unions of cells.
7. density_unique: equality of every finite conditional average plus the
   independently derived strong convergence rate.
8. mass_symmetric_difference_bound: square the mass difference and compare
   with C*lambda(symdiff). Obtain a precision schedule without a square-root
   evaluator.

A global cap requires no new hypothesis:
C=H_{R(0)}+1 bounds all energies by the precision-zero tail estimate and
monotonicity. Pick integer J≥1 with J²≥C; set approximation error
4^(−p)/J² suffices for mass-value error 2^(−p).

### Energy-rate producer

Given L≥0 and certified sibling differences at most L*2^(−n), use

(u²+v²)/2 - ((u+v)/2)² = (u-v)²/4

to prove a one-level increment bound. Telescope with the finite geometric
sum. It follows that H_m-H_n≤(L²/3)4^(−n).
Choose h with L≤2^h and set EnergyRate.rate(p)=p+h.
This derives a density from mass regularity, instead of assuming one.

## 6. Energy metastability

For a fixed primitive recursive g, let
t(0)=0 and t(j+1)=max(t(j),g(t(j))).
For integer C0≥H_n, set B=C0*4^p+1.
Search the bounded list j<B for an endpoint increment at most 4^(−p).
Maintain the telescoping energy invariant and a Boolean good-index flag.

The cap forces successful search. Monotonicity bounds every pair of
interior indices. Its finite conclusion is

∃ N≤t(B), ∀ m,n≤max(N,g(N)), N≤m → N≤n → distance(d_m,d_n)≤2^(−p).

Its bounded quantifiers can be Booleanized. Do not replace it by a full
Cauchy modulus: the halting-family construction in the report prohibits a
uniform computable conversion from a cap alone.

## 7. Boolean unions

A BooleanName is a rapid L1Name all of whose approximants contain only 0,1.
Define complement, union, intersection and difference coordinatewise on a
common refinement. Prove the 1-Lipschitz-per-input inequalities first.

For a uniformly given sequence A_i and finite tail certificates T(p), use
N=T(p+2), h=p+2+ceilLog2(max(1,N)), and output the union of the first N
h-precision approximants. Compare two outputs with the common *finite*
prefix of length max(T(p+2),T(q+2)); no infinite union is assumed.
This gives the rapid rate. Prove the least-upper-bound property for the
order lambda(A\B)=0, then derive countable additivity for disjoint inputs.
The batch producer's clock is part of the contract.

## 8. Repository integration

Pinned source commit: b2341af5370cd8a43f72ebb2341c0d7d7395b634.

Reuse the inspected internal common-envelope kernel at:

Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Probability/TruncationEstimate.lean

Its truncation theorem is already an internal iPRA sum inequality.
Its documentation explicitly excludes normalization and refinement.
The corrected separate-tail shortcut instead occurs at:

Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/expected_value_ipra_2026-11-16/paper/sections/12_convergence.tex

The existing internal theorem is sound and is not the object of the
correction. Add normalized dyadic-step adapters, the excess-tail inequality,
and energy identities as new modules; then compile precision schedules and
completion statements through the actual Prf PRAAx interface.
Host rational truth is not a substitute for this last compilation.
