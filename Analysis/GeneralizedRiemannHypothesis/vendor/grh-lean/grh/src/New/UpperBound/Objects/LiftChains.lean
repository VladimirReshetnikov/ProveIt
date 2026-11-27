import Lib.General.LinearAlgebra.BlockEmbeddings
import Lib.Shimura.HeckeTower.HeckeData
import Lib.Weil.CompactLift.ThetaKernelDefs
import New.Reduction.Data.Sizes
import New.UpperBound.Objects.LabelsAndIndexTypes
import New.UpperBound.Objects.LiftLawsModuloN

/-!
# Chains of theta lifts, jointly invariant combinations, and free levels

This file treats chains of theta lifts and their jointly invariant combinations for a general
tower of finite adelic unitary groups joined by theta kernels. It shows that, in bounded rank, the
levels that reduce to `1` at the chosen places are free, that is, that they have trivial
stabilisers `New.classAut`. The chosen places of `E = D.E` are the prime divisors of
`New.Data.piM`; `D.f` is the number of infinite places of `E`. For every integral level in bounded
rank, the orders of the stabilisers divide `New.Data.chosenGroupOrder`.

## Main definitions and results

* `New.chain`: the composite of the first `j` lifts. It is equivariant (`New.chain_equivariant`),
  and its values are linear in the pure tensor of the data
  (`New.exists_linearMap_chain_eq_apply_pure`).
* `New.IsJointlyInvariant.sum_chain_mem_nsmul`: at free levels, a jointly invariant combination of
  chains is a sum with one term for each tuple of double cosets, with no denominators.
* `New.Data.principalLevel_le_chosenLevel`, `New.Data.classAut_eq_bot_of_le_chosenLevel`: in bounded
  rank, levels that reduce to `1` at the chosen places are free.
* `New.Data.card_classAut_dvd_chosenGroupOrder`: in rank at most `2 * D.n D.m` and for every
  integral level the stabilisers have order dividing `chosenGroupOrder`.

Notions from other files:
* `New.TensorChain`: The complex tensor product S_{j−1} ⊗ ⋯ ⊗ S_0, equal to ℂ for j = 0.
* `New.classAut`: `classAut Γ K g` is Γ ∩ gKg⁻¹, the stabiliser in Γ of the coset gK; here
  Γ = `stdRatPoints` is the rational unitary group of the standard definite space `New.stdSpace`,
  inside the finite adelic group.
* `New.Data.n`: The rank 𝗇_j = k + j(t + 1) of X_j.
-/

noncomputable section

/-!
## Chains of theta lifts and jointly invariant combinations

A tower of finite adelic unitary groups `Gf E (n j)` is joined by theta kernels `k j`
(`New.Kernel`). Each kernel lifts forms on `Gf E (n j)` to forms on `Gf E (n (j + 1))`
(`New.Kernel.lift`). The forms of stage `j` take values in the Weyl module
`WeylIndex (n j) κ → ℂ` of weight `(κ, e j)`. The kernel `k j` has a space of data `S j`, an action
`ω` of the pair of groups on `S j`, and a map `jetMap` that sends a datum to a linear map from the
Weyl module of stage `j` to that of stage `j + 1`.

For a set `A`, `n • A` is the set of sums of `n` elements of `A`.
-/

namespace New

open Finset Pointwise TensorProduct TensorChain Kernel

variable {E : Type} {M : Type*} [Field E] [CMType E] [AddCommGroup M] [Module ℚ M]
  [Module ℂ M] {n S : ℕ → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  [∀ j, AddCommGroup (S j)] [∀ j, Module ℂ (S j)] {κ : NumberField.InfinitePlace E → ℕ → ℕ}
  {e : ℕ → NumberField.InfinitePlace E → ℤ} {K : (j : ℕ) → Subgroup (Gf E (n j))}
  (k : ∀ j : ℕ, Kernel (n j) (n (j + 1)) κ (e j) (e (j + 1)) (K j) (S j)) [∀ j, IsLevel (K j)]

/-- The chain of j theta lifts with data Φ_0, …, Φ_{j−1}. It is the composite linear map from
algebraic forms of stage 0 to algebraic forms of stage j. The forms `AlgForm (n j) κ (e j)` of
stage j are the smooth functions on `Gf E (n j)` that transform under the rational points by the
weight with `κ τ h` columns of height `h` and the power `e j τ` of the determinant at `τ`. -/
def chain (Φ : (j : ℕ) → S j) : ∀ j : ℕ, AlgForm (n 0) κ (e 0) →ₗ[ℂ] AlgForm (n j) κ (e j) :=
  compUpTo fun j ↦ (k j).lift (Φ j)

/-- Equivariance of the chain of lifts. For each `j`, `k j` is a theta kernel with data `S j` from
algebraic forms on `Gf E (n j)` of weight `(κ, e j)` to forms on `Gf E (n (j + 1))` of weight
`(κ, e (j + 1))`. Its lift `(k j).lift` sends a datum and a form to the lifted form. Its action
`(k j).ω` is an action of `Gf E (n j) × Gf E (n (j + 1))` on `S j`. The chain `lift` applies the
first `m` lifts in turn to a form `φ`, using the factors of a tensor `t` of data. Let `a j` lie in
`Gf E (n j)` for every `j`, and move each factor `j` of `t` by `(k j).ω (a j, a (j + 1))`. The chain
with the moved data, applied to the right translate of `φ` by `a 0`, is the right translate by `a m`
of the chain with the data `t` applied to `φ`. -/
theorem TensorChain.lift_kernelLift_map_omega [WeilData E] (a : ∀ j : ℕ, Gf E (n j))
    (φ : AlgForm (n 0) κ (e 0)) (m : ℕ) (t : TensorChain S m) :
    lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (a 0) φ) m
        (map (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) m t) =
      algFormRep κ (e m) (a m) (lift (fun i : ℕ ↦ (k i).lift) φ m t) := by
  induction m with
  | zero =>
    -- A tensor of length `0` is a scalar `c`, and both sides are `c` times the translate of `φ`.
    change ((show ℂ from t) * 1) • algFormRep κ (e 0) (a 0) φ =
      algFormRep κ (e 0) (a 0) ((show ℂ from t) • φ)
    rw [mul_one, map_smul]
  | succ m ih =>
    -- Both sides are linear in `t`; on `s ⊗ r` use the equivariance of the last lift.
    have h_tmul (s : S m) (r : TensorChain S m) :
        (k m).lift ((k m).ω (a m, a (m + 1)) s)
            (lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (a 0) φ) m
              (map (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) m r)) =
          algFormRep κ (e (m + 1)) (a (m + 1))
            ((k m).lift s (lift (fun i : ℕ ↦ (k i).lift) φ m r)) := by
      rw [ih r, lift_equivariant]
    have h_maps : lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (a 0) φ) (m + 1) ∘ₗ
          map (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) (m + 1) =
        algFormRep κ (e (m + 1)) (a (m + 1)) ∘ₗ lift (fun i : ℕ ↦ (k i).lift) φ (m + 1) :=
      TensorProduct.ext' (M := S m) (N := TensorChain S m) h_tmul
    exact LinearMap.congr_fun h_maps t

/-- Moving an element to the source of a chain of lifts. Let `z i` lie in the group of stage `i`,
with `ω(z i, z (i + 1)) = 1` for every lift, let `t` be any tensor of the data of the first `m`
lifts, and let `j < m`. If `ω(1, z (j + 1))`, acting alone on the factor of the lift from stage
`j` to stage `j + 1`, fixes `t`, then the chain with data `t` has the same value at `φ` and at
the right translate of `φ` by `z 0`. -/
theorem TensorChain.lift_algFormRep_of_map_eq [WeilData E] {z : ∀ i : ℕ, Gf E (n i)}
    (hz : ∀ i : ℕ, (k i).ω (z i, z (i + 1)) = 1) {m j : ℕ} (hj : j < m) {t : TensorChain S m}
    (h_fix : map (fun i : ℕ ↦ if i = j then (k i).ω (1, z (i + 1)) else 1) m t = t)
    (φ : AlgForm (n 0) κ (e 0)) :
    lift (fun i : ℕ ↦ (k i).lift) (algFormRep κ (e 0) (z 0) φ) m t =
      lift (fun i : ℕ ↦ (k i).lift) φ m t := by
  -- As every `ω(z i, z (i + 1))` is trivial, `ω(1, z (j + 1))` on factor `j` is the action of the
  -- tuple `a` that is `(z i)⁻¹` up to stage `j` and `1` after it.
  set a : ∀ i : ℕ, Gf E (n i) := fun i ↦ if i ≤ j then (z i)⁻¹ else 1 with ha
  have h_absorb (i : ℕ) (g : Gf E (n i)) (g' : Gf E (n (i + 1))) :
      (k i).ω (g, g') = (k i).ω (g * z i, g' * z (i + 1)) := by
    rw [← Prod.mk_mul_mk, map_mul, hz i, mul_one]
  have h_factors : (fun i : ℕ ↦ (k i).ω (a i, a (i + 1))) =
      fun i : ℕ ↦ if i = j then (k i).ω (1, z (i + 1)) else 1 := by
    funext i
    rcases lt_trichotomy i j with h_lt | rfl | h_gt
    · simpa [ha, h_lt.le, h_lt.ne, Nat.succ_le_of_lt h_lt, Prod.mk_one_one] using
        h_absorb i (a i) (a (i + 1))
    · simpa [ha] using h_absorb i (z i)⁻¹ 1
    · simp [ha, h_gt.not_ge, h_gt.ne', (Nat.lt_succ_of_lt h_gt).not_ge, Prod.mk_one_one]
  have h_equivariant := lift_kernelLift_map_omega k a (algFormRep κ (e 0) (z 0) φ) m t
  rw [h_factors, h_fix] at h_equivariant
  simpa [ha, hj.not_ge] using h_equivariant.symm

/-- Let `φ` be fixed by the level `K 0`, and let each `a j` lie in `K j`. Acting on each datum `Φ i`
by `(a i, a (i + 1))` and applying the chain to `φ` gives the right translate by `a j` of the chain
applied to `φ`. -/
lemma chain_equivariant [WeilData E] {φ : AlgForm (n 0) κ (e 0)}
    (hφ : φ ∈ levelSpace (algFormRep κ (e 0)) (K 0)) (a : ∀ j : ℕ, K j)
    (Φ : (j : ℕ) → S j) (j : ℕ) :
    chain k (fun i : ℕ ↦ (k i).ω (a i, (a (i + 1)).val) (Φ i)) j φ =
      algFormRep κ (e j) (a j).val (chain k Φ j φ) := by
  have h_fix : algFormRep κ (e 0) (a 0).val φ = φ := by simpa using hφ (a 0)
  simpa [chain, h_fix] using lift_kernelLift_map_omega k (fun i : ℕ ↦ (a i).val) φ j (pure Φ j)

/-- The chain of p pairs of theta lifts, the i-th pair with datum Φ_i in S_{2i} ⊗ S_{2i+1}: a
linear map from forms of stage 0 to forms of stage 2p. -/
def doubleLiftChain (Φ : (j : ℕ) → S (2 * j) ⊗[ℂ] S (2 * j + 1)) :
    ∀ p : ℕ, AlgForm (n (2 * 0)) κ (e (2 * 0)) →ₗ[ℂ] AlgForm (n (2 * p)) κ (e (2 * p)) :=
  compUpTo fun i ↦ liftInPairs (fun j ↦ (k j).lift) i (Φ i)

/-- For a_j in `Gf E (n j)`, the operator ω(a_{2i}, a_{2i+1}) ⊗ ω(a_{2i+1}, a_{2i+2}) on the space
S_{2i} ⊗ S_{2i+1}. -/
def twoKernelAction (a : ∀ j : ℕ, Gf E (n j)) (i : ℕ) :
    S (2 * i) ⊗[ℂ] S (2 * i + 1) →ₗ[ℂ] S (2 * i) ⊗[ℂ] S (2 * i + 1) :=
  map ((k (2 * i)).ω (a (2 * i), a (2 * i + 1)))
    ((k (2 * i + 1)).ω (a (2 * i + 1), a (2 * i + 1 + 1)))

/-- Fix `φ` and `g`. The value at `g` of the chain applied to `φ` is a linear function
`β : TensorChain S j →ₗ[ℂ] (WeylIndex (n j) κ → ℂ)` of the pure tensor `Φ (j - 1) ⊗ ⋯ ⊗ Φ 0` of the
data. -/
lemma exists_linearMap_chain_eq_apply_pure (j : ℕ) (φ : AlgForm (n 0) κ (e 0)) (g : Gf E (n j)) :
    ∃ β : TensorChain S j →ₗ[ℂ] WeylIndex (n j) κ → ℂ, ∀ Φ : (j : ℕ) → S j,
      (chain k Φ j φ).val g = β (TensorChain.pure Φ j) :=
  -- `β` is the linear map `TensorChain.lift` of the lifts at `φ`, followed by evaluation at `g`
  ⟨.proj g ∘ₗ Submodule.subtype _ ∘ₗ lift (fun i : ℕ ↦ (k i).lift) φ j, by simp [chain]⟩

/-- Joint invariance: the tensor ∑_{x∈s} L_x ⊗ Φ_{x,m−1} ⊗ ⋯ ⊗ Φ_{x,0} is unchanged by the joint
action of every tuple a with a_j ∈ K_j and a_j = 1 for j ≥ m, as tested against all linear maps β
from S_{m−1} ⊗ ⋯ ⊗ S_0 to the Weyl module `WeylIndex (n m) κ → ℂ` of stage m. Here a acts on Φ_{x,j}
by ω(a_j, a_{j+1}), and the coefficients L_x are linear maps from that Weyl module to `M`. -/
def IsJointlyInvariant {X : Type*} (m : ℕ) (s : Finset X) (L : X → (WeylIndex (n m) κ → ℂ) →ₗ[ℂ] M)
    (Φ : X → ∀ j : ℕ, S j) : Prop :=
  ∀ a : ∀ j : ℕ, K j, (∀ j ≥ m, a j = 1) → ∀ β : TensorChain S m →ₗ[ℂ] WeylIndex (n m) κ → ℂ,
    ∑ x ∈ s, L x (β (TensorChain.pure (fun j : ℕ ↦ (k j).ω (a j, a (j + 1)) (Φ x j)) m)) =
      ∑ x ∈ s, L x (β (TensorChain.pure (Φ x) m))

/-- Representatives of the classes `c j` for `j < m`, followed by the points `g j` for `m ≤ j`. -/
def classPoints {m : ℕ} (c : ∀ j : Fin m, StdClasses (K j)) (g : ∀ j : ℕ, Gf E (n j)) (j : ℕ) :
    Gf E (n j) :=
  if h : j < m then (c ⟨j, h⟩).out else g j

omit [∀ j, IsLevel (K j)] in
lemma classPoints_of_le {m j : ℕ} (c : ∀ j : Fin m, StdClasses (K j)) (g : ∀ j : ℕ, Gf E (n j))
    (h_le : m ≤ j) : classPoints c g j = g j := dite_eq_right h_le.not_gt

/-- The product of the first `m` kernels, applied to the value of `φ` at `g 0`. Factor `j` is the
linear map `jetMap` between the Weyl modules of stages `j` and `j + 1` that belongs to the datum
`Φ j` moved by the action `ω` of the pair of points `(g j, g (j + 1))`. -/
def kernelProduct (Φ : (j : ℕ) → S j) (φ : AlgForm (n 0) κ (e 0)) (g : ∀ j : ℕ, Gf E (n j))
    (m : ℕ) : WeylIndex (n m) κ → ℂ :=
  compUpTo (fun j ↦ (k j).jetMap ((k j).ω (g j, g (j + 1)) (Φ j))) m (φ.val (g 0))

omit [∀ j, IsLevel (K j)] in
/-- The product of `m + 1` kernels is the last kernel applied to the product of the first `m`. -/
lemma kernelProduct_succ (Φ : ∀ j : ℕ, S j) (φ : AlgForm (n 0) κ (e 0))
    (g : ∀ j : ℕ, Gf E (n j)) (m : ℕ) :
    kernelProduct k Φ φ g (m + 1) =
      (k m).jetMap ((k m).ω (g m, g (m + 1)) (Φ m)) (kernelProduct k Φ φ g m) := rfl

omit [Module ℚ M] [Module ℂ M] in
/-- A sum over tuples of `m + 1` double cosets, sorted by the last one. For a tuple `c` of classes
`c j` in `StdClasses (K j)`, the family `classPoints c g` lists their chosen representatives and
continues with the points `g j`. The sum of `F` over the tuples of length `m + 1` is the sum, over
the last class `r`, of the sums over the tuples of length `m`, where the point `g m` is replaced by
the representative `r.out`. -/
lemma sum_classPoints_succ (m : ℕ) (F : (∀ j : ℕ, Gf E (n j)) → M) (g : ∀ j : ℕ, Gf E (n j)) :
    ∑ c : ∀ j : Fin (m + 1), StdClasses (K j), F (classPoints c g) =
      ∑ r : StdClasses (K m), ∑ c : ∀ j : Fin m, StdClasses (K j),
        F (classPoints c (Function.update g m r.out)) := by
  rw [← Fintype.sum_prod_type']
  -- a tuple of `m + 1` classes is a last class with a tuple of `m` classes
  refine Fintype.sum_equiv (Fin.snocEquiv fun j : Fin (m + 1) ↦ StdClasses (K j)).symm _ _
    fun c ↦ congrArg F (funext fun j ↦ ?_)
  obtain h_lt | rfl | h_gt := lt_trichotomy j m
  · simp [classPoints, h_lt, h_lt.trans m.lt_succ_self, Fin.init]
  · simp [classPoints, Fin.last]
  · simp [classPoints, h_gt.not_gt, Nat.not_lt.2 h_gt, h_gt.ne']

/-- **A chain of lifts is a plain sum.** Let `k j` be theta kernels from stage `j` to stage `j + 1`,
and let `φ : AlgForm (n 0) κ (e 0)` be an algebraic form of stage `0` fixed by the level `K 0`. Let
`∑ x ∈ s, L x ⊗ Φ x` be jointly invariant: it is unchanged when elements `a j ∈ K j`, `j < m`, move
each datum `Φ x j` by `ω(a j, a (j + 1))`, with `a m = 1`. Let the levels `K j`, `j < m`, have
trivial stabilisers `classAut`. Then ∑_x L_x(value at `g m` of the chain with data `Φ x` applied to
`φ`) is the sum, over tuples `c` of double cosets `StdClasses (K j)`, `j < m`, of ∑_x
L_x(`kernelProduct`). -/
theorem IsJointlyInvariant.sum_chain_eq_sum_kernelProduct [WeilData E]
    {X : Type*} {m : ℕ} {s : Finset X}
    {L : X → (WeylIndex (n m) κ → ℂ) →ₗ[ℂ] M} {Φ : X → ∀ j : ℕ, S j}
    (h_inv : IsJointlyInvariant k m s L Φ)
    (h_free : ∀ j < m, ∀ g : Gf E (n j), classAut stdRatPoints (K j) g = ⊥)
    {φ : AlgForm (n 0) κ (e 0)} (hφ : φ ∈ levelSpace (algFormRep κ (e 0)) (K 0))
    (g : ∀ j : ℕ, Gf E (n j)) :
    ∑ x ∈ s, L x ((chain k (Φ x) m φ).val (g m)) =
      ∑ c : ∀ j : Fin m, StdClasses (K j), ∑ x ∈ s,
        L x (kernelProduct k (Φ x) φ (classPoints c g) m) := by
  -- The integral over all points is taken one variable at a time, by induction on the length of
  -- the chain. The last lift is an integral whose integrand is constant on classes, and each class
  -- has volume `1`; each value of the integrand is a shorter chain.
  induction m generalizing g with
  | zero => simp [kernelProduct, classPoints, chain, compUpTo]
  | succ j ih =>
    -- `T a β` applies `β` to the first `j` factors, then the kernel at `(a, g (j + 1))` with the
    -- last one.
    let T (a : Gf E (n j)) (β : TensorChain S j →ₗ[ℂ] WeylIndex (n j) κ → ℂ) :
        TensorChain S (j + 1) →ₗ[ℂ] WeylIndex (n (j + 1)) κ → ℂ :=
      lift ((k j).jetMap.compl₁₂ ((k j).ω (a, g (j + 1))) β)
    have hT (a : Gf E (n j)) (β : TensorChain S j →ₗ[ℂ] WeylIndex (n j) κ → ℂ)
        (f : ∀ i : ℕ, S i) :
        T a β (pure f (j + 1)) = (k j).jetMap ((k j).ω (a, g (j + 1)) (f j)) (β (pure f j)) :=
      lift.tmul _ (pure f j)
    -- `F` is the integrand of the last lift, summed over `x`.
    let integrand (x : X) (a : Gf E (n j)) : WeylIndex (n (j + 1)) κ → ℂ :=
      (k j).jetMap ((k j).ω (a, g (j + 1)) (Φ x j)) ((chain k (Φ x) j φ).val a)
    let F (a : Gf E (n j)) : M := ∑ x ∈ s, L x (integrand x a)
    have h_integral : classIntegral stdRatPoints (K j) F =
        ∑ x ∈ s, L x ((chain k (Φ x) (j + 1) φ).val (g (j + 1))) :=
      classIntegral_sum (f := integrand) s (fun x : X ↦ (L x).toAddMonoidHom) (fun _ ↦ 1)
        (fun x ↦ (k j).integrand_mem_smoothInvariants ..) (by simp [F])
    -- The integrand is right `K j`-invariant: joint invariance for `b` in the slot `j` alone.
    have h_const : K j ≤ rightStabilizer F := fun b hb a ↦ by
      -- `β` is the linear map that gives the value at `a` of the chain of length `j`.
      obtain ⟨β, hβ⟩ := exists_linearMap_chain_eq_apply_pure k j φ a
      have h_eq := h_inv (Pi.mulSingle j ⟨b, hb⟩) (by simp +contextual [ne_of_gt]) (T a β)
      simp only [hT, ← hβ, chain_equivariant k hφ] at h_eq
      simpa [F, integrand, omega_omega] using h_eq
    have h_classes : classIntegral stdRatPoints (K j) F = ∑ r : StdClasses (K j), F r.out := by
      rw [classIntegral_eq_classSum h_const, classSum, finsum_eq_sum_of_fintype]
      exact sum_congr rfl fun r _ ↦ by simp [h_free j]
    rw [← h_integral, h_classes,
      sum_classPoints_succ j fun p ↦ ∑ x ∈ s, L x (kernelProduct k (Φ x) φ p (j + 1))]
    refine sum_congr rfl fun r _ ↦ ?_
    -- The value at `r` is a chain of length `j`, with the kernel absorbed in the coefficients.
    let L' (x : X) : (WeylIndex (n j) κ → ℂ) →ₗ[ℂ] M :=
      L x ∘ₗ (k j).jetMap ((k j).ω (r.out, g (j + 1)) (Φ x j))
    have h_inv' : IsJointlyInvariant k j s L' Φ := fun a ha β ↦ by
      simpa [L', hT, ha, Prod.mk_one_one] using h_inv a (fun i hi ↦ ha i (by omega)) (T r.out β)
    simpa [F, integrand, L', kernelProduct, classPoints, compUpTo] using
      ih h_inv' (fun i hi ↦ h_free i (by omega)) (Function.update g j r.out)

omit [∀ j, IsLevel (K j)] in
/-- Let `P j g v` be a property of a point `g` of the group of stage `j` and a vector `v` of the
Weyl module of stage `j`. If `P` holds for the values of the form `φ`, and each of the first `m`
kernels `k j` with datum `Φ j` takes vectors with `P` at stage `j` to vectors with `P` at stage
`j + 1`, then `P` holds for the product `kernelProduct` of these kernels at any tuple of points. -/
lemma kernelProduct_induction (P : ∀ j : ℕ, Gf E (n j) → (WeylIndex (n j) κ → ℂ) → Prop)
    {Φ : ∀ j : ℕ, S j} {m : ℕ}
    (h_step : ∀ j < m, ∀ (g : Gf E (n j)) (g' : Gf E (n (j + 1))) (v : WeylIndex (n j) κ → ℂ),
      P j g v → P (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ j)) v))
    {φ : AlgForm (n 0) κ (e 0)} (h_base : ∀ g : Gf E (n 0), P 0 g (φ.val g))
    (g : ∀ j : ℕ, Gf E (n j)) :
    P m (g m) (kernelProduct k Φ φ g m) := by
  induction m with
  | zero => exact h_base (g 0)
  | succ j ih => exact h_step j j.lt_succ_self _ _ _ (ih fun i hi ↦ h_step i (by omega))

omit [∀ j, IsLevel (K j)] in
/-- Let `size j g v` be a size of a vector `v` of the Weyl module of stage `j` at a point `g`, and
let `r j ≥ 0` for every `j`. If the kernel `k j` with datum `Φ j` multiplies the size by at most
`r j` for `j < m`, and the values of the form `φ` have size at most `B`, then the product
`kernelProduct` of the first `m` kernels has size at most `(∏ j < m, r j) * B`. -/
lemma apply_kernelProduct_le_prod_mul (size : ∀ j : ℕ, Gf E (n j) → (WeylIndex (n j) κ → ℂ) → ℝ)
    {r : ℕ → ℝ} (hr : ∀ j : ℕ, 0 ≤ r j) {Φ : ∀ j : ℕ, S j} {m : ℕ}
    (h_step : ∀ j < m, ∀ (g : Gf E (n j)) (g' : Gf E (n (j + 1))) (v : WeylIndex (n j) κ → ℂ),
      size (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ j)) v) ≤ r j * size j g v)
    {φ : AlgForm (n 0) κ (e 0)} {B : ℝ} (h_base : ∀ g : Gf E (n 0), size 0 g (φ.val g) ≤ B)
    (g : ∀ j : ℕ, Gf E (n j)) :
    size m (g m) (kernelProduct k Φ φ g m) ≤ (∏ j ∈ range m, r j) * B := by
  refine kernelProduct_induction k (fun j g v ↦ size j g v ≤ (∏ i ∈ range j, r i) * B)
    (fun j hj g g' v hv ↦ ?_) (by simpa using h_base) g
  calc size (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ j)) v)
      ≤ r j * size j g v := h_step j hj g g' v
    _ ≤ r j * ((∏ i ∈ range j, r i) * B) := mul_le_mul_of_nonneg_left hv (hr j)
    _ = (∏ i ∈ range (j + 1), r i) * B := by rw [prod_range_succ_comm, mul_assoc]

/-- Let `φ : AlgForm (n 0) κ (e 0)` be an algebraic form of stage `0` fixed by the level `K 0`. Let
`∑ x ∈ s, L x ⊗ Φ x` be jointly invariant for the theta kernels `k j`: it is unchanged when
`a j ∈ K j`, `j < m`, move each datum `Φ x j` by `ω(a j, a (j + 1))`, with `a m = 1`. Let the levels
`K j`, `j < m`, have trivial stabilisers `classAut`. Let the property `P` hold for the values of
`φ`, and let each kernel preserve `P`. Let `p` be a point of the group of stage `m`, and let
`∑ x ∈ s, L x (v x)` lie in `A` whenever the vectors `v x` have `P` at `p` and are the images of the
pure tensors of the data `Φ x` under one linear map. Then the value at `p` of the combination of the
chains applied to `φ` is a sum of elements of `A`, one for each tuple of double cosets in
`StdClasses (K j)`, `j < m`. -/
lemma IsJointlyInvariant.sum_chain_mem_nsmul [WeilData E] {X : Type*} {m : ℕ} {s : Finset X}
    {L : X → (WeylIndex (n m) κ → ℂ) →ₗ[ℂ] M} {Φ : X → ∀ j : ℕ, S j}
    (h_inv : IsJointlyInvariant k m s L Φ)
    (h_free : ∀ j < m, ∀ g : Gf E (n j), classAut stdRatPoints (K j) g = ⊥)
    {φ : AlgForm (n 0) κ (e 0)} (hφ : φ ∈ levelSpace (algFormRep κ (e 0)) (K 0))
    (P : ∀ j : ℕ, Gf E (n j) → (WeylIndex (n j) κ → ℂ) → Prop)
    (h_step : ∀ x ∈ s, ∀ j < m, ∀ (g : Gf E (n j)) (g' : Gf E (n (j + 1)))
      (v : WeylIndex (n j) κ → ℂ),
      P j g v → P (j + 1) g' ((k j).jetMap ((k j).ω (g, g') (Φ x j)) v))
    (h_base : ∀ g : Gf E (n 0), P 0 g (φ.val g)) {p : Gf E (n m)} {A : Set M}
    (hA : ∀ β : TensorChain S m →ₗ[ℂ] WeylIndex (n m) κ → ℂ,
      let v (x : X) : WeylIndex (n m) κ → ℂ := β (pure (Φ x) m)
      (∀ x ∈ s, P m p (v x)) → ∑ x ∈ s, L x (v x) ∈ A) :
    ∑ x ∈ s, L x ((chain k (Φ x) m φ).val p) ∈
      (∏ j ∈ range m, Nat.card (StdClasses (K j))) • A := by
  obtain ⟨g, rfl⟩ : ∃ g : ∀ j : ℕ, Gf E (n j), g m = p := ⟨Pi.mulSingle m p, by simp⟩
  have h_term (c : ∀ j : Fin m, StdClasses (K j)) :
      ∑ x ∈ s, L x (kernelProduct k (Φ x) φ (classPoints c g) m) ∈ A := by
    let q : ∀ j : ℕ, Gf E (n j) := classPoints c g
    -- The product of the kernels is linear in the tensor of the data.
    let β : TensorChain S m →ₗ[ℂ] WeylIndex (n m) κ → ℂ :=
      lift (fun j : ℕ ↦ (k j).jetMap ∘ₗ (k j).ω (q j, q (j + 1))) (φ.val (q 0)) m
    have hβ (x : X) : β (pure (Φ x) m) = kernelProduct k (Φ x) φ q m := by simp [β, kernelProduct]
    simpa only [hβ] using hA β fun x hx ↦ by
      simpa [hβ, q, classPoints_of_le] using kernelProduct_induction k P (h_step x hx) h_base q
  rw [h_inv.sum_chain_eq_sum_kernelProduct k h_free hφ g]
  simpa [prod_range] using Set.finsetSum_mem_finsetSum univ _ _ fun c _ ↦ h_term c

end New

/-!
## Chosen places, the chosen group order and free levels

These are facts on the places of `E` that the data single out: the places above the level prime
`D.N`, and the chosen places, with `D.ChosenPlace i` the chosen places above the prime
p_i = `D.levelPrime i`. The map `D.chosenPlace` sends a pair `(i, w)` to the place `w`.

* `New.Data.chosenGroupOrder`: the order of the product of the groups `GL (r t)` over the residue
  fields at the chosen places.
* `New.Data.card_pi_GL_chosenPlace`, `New.Data.log_chosenGroupOrder_le`: the order of such a product
  in terms of the primes p_i, and the bound `log chosenGroupOrder ≤ D.x ^ 32`.
-/

namespace New.Data

open Parameters Real Finset Subgroup Fintype Function Embedding

variable {P : Parameters} {D : Data P} (i : Fin 2) {w : FinPlace D.E} {n : Type} [Fintype n]
  [DecidableEq n]

/-! ### Places above the level and chosen places -/

/-- The infinite places `D.Φ` of E are in bijection with the chosen places above the prime
p_i = `D.levelPrime i`. -/
lemma nonempty_infinitePlace_equiv_chosenPlace (i : Fin 2) : Nonempty (D.Φ ≃ D.ChosenPlace i) := by
  obtain ⟨c, h_norm, h_coprime⟩ := D.exists_piM_mul_star_eq_levelPrime_mul_coprime (i := i)
  exact nonempty_infinitePlace_equiv_finPlace (levelPrime_modEq_one D i) h_norm h_coprime

/-- A chosen bijection from the infinite places of E to the chosen places above p_i. -/
def chosenEquiv : D.Φ ≃ D.ChosenPlace i := (nonempty_infinitePlace_equiv_chosenPlace i).some

lemma card_chosenPlace : Fintype.card (D.ChosenPlace i) = D.f :=
  (card_congr (D.chosenEquiv i)).symm

/-- The level prime N is a uniformiser at each finite place w of E above it: its valuation in the
completion at w is exp(−1). -/
lemma v_N_eq_exp_neg_one (hN_mem : ↑D.N ∈ w.asIdeal) :
    Valued.v (D.N : LocField w) = WithZero.exp (-1) := by
  simpa [← v_algebraMap_eq_intValuation] using
    intValuation_natCast_eq_exp_neg_one hN_mem (not_dvd_q₁_mul_d_of_modEq_one D.N_modEq_one)

/-- The equation π π̄ = N for π = `D.piN`, with the cofactor `1` written out, as the lemmas on
primes `≡ 1` modulo `P.q₁ D.towerExp * P.d` take it. -/
lemma piN_mul_star_eq_N_mul_one : D.piN * star D.piN = D.N * (1 : ℕ) := by simp [D.piN_mul_star]

/-- The factor π = `D.piN` of the level N = π π̄ is a uniformiser at each finite place `w` that
divides it: if `D.piN ∈ w`, then `w.intValuation D.piN = exp (-1)`. -/
lemma intValuation_piN (hπ_mem : D.piN ∈ w.asIdeal) : w.intValuation D.piN = WithZero.exp (-1) := by
  -- `π * star π = N`, so `w` lies above `N`, and the cofactor of `N` is `1`.
  refine intValuation_eq_of_mul_star D.N_modEq_one ?_ D.piN_mul_star_eq_N_mul_one
    D.N.coprime_one_right hπ_mem
  simpa [D.piN_mul_star] using w.asIdeal.mul_mem_right (star D.piN) hπ_mem

/-- The integer `D.piM`, whose prime divisors are the chosen places, is a uniformiser at each place
that divides it. -/
lemma intValuation_piM (hπ_mem : D.piM ∈ w.asIdeal) :
    w.intValuation D.piM = WithZero.exp (-1) := by
  -- `w` lies above one of the two primes `p = D.levelPrime k`, and `D.piM * star D.piM` is `p`
  -- times a number prime to `p`.
  obtain ⟨k, -, hp_mem⟩ := (D.isChosen_iff (w := w)).1 hπ_mem
  obtain ⟨c, h_norm, h_coprime⟩ :
      ∃ c : ℕ, D.piM * star D.piM = D.levelPrime k * c ∧ (D.levelPrime k).Coprime c :=
    D.exists_piM_mul_star_eq_levelPrime_mul_coprime
  exact intValuation_eq_of_mul_star (levelPrime_modEq_one D k) hp_mem h_norm h_coprime hπ_mem

/-- The product, over the chosen places above `D.levelPrime 0` and `D.levelPrime 1`, of the orders
of the groups `GL (r t)` over the residue fields, for the rank r = `D.r` and t = `D.t` = 5 r. It is
a common multiple of the orders of the stabilisers in
`New.Data.card_classAut_dvd_chosenGroupOrder`. -/
def chosenGroupOrder : ℕ :=
  Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL (Fin (D.r * D.t)) (ResField (D.chosenPlace x)))
  deriving NeZero

/-- The norms `w.q` of the chosen places `w` above p₀ and p₁ have product M^f, where
M = `D.M` = p₀ p₁ and f = `D.f` is the number of infinite places of E. -/
lemma prod_q_chosenPlace : ∏ x : (i : Fin 2) × D.ChosenPlace i,
  (D.chosenPlace x).q = D.M ^ D.f := by
  -- There are `f` chosen places above p_i, each of norm p_i.
  have h_norm (i : Fin 2) (w : D.ChosenPlace i) : w.val.q = D.levelPrime i :=
    D.q_eq_levelPrime w.property.right
  simp [chosenPlace, Fintype.prod_sigma, h_norm, card_chosenPlace, Data.M, mul_pow]

/-- At a chosen place `w` above the prime p_i = `D.levelPrime i`, the group GL_l over the residue
field at `w` has the same order as GL_l over the field with p_i elements. -/
lemma card_GL_resField_eq_card_GL_zmod (w : D.ChosenPlace i) (l : ℕ) :
    Nat.card (GL (Fin l) (ResField w.val)) = Nat.card (GL (Fin l) (ZMod (D.levelPrime i))) := by
  -- The residue field has p_i elements, and p_i is prime, so it is isomorphic to
  -- `ZMod (D.levelPrime i)`.
  have : Fintype (ResField w.val) := Fintype.ofFinite _
  have h_card : Fintype.card (ResField w.val) = D.levelPrime i := by
    rw [Fintype.card_eq_nat_card, card_ResField, D.q_eq_levelPrime w.property.right]
  have e : ZMod (D.levelPrime i) ≃+* ResField w.val :=
    ZMod.ringEquivOfPrime _ (D.levelPrime_prime i) h_card
  exact Nat.card_congr (Units.mapEquiv e.symm.mapMatrix.toMulEquiv).toEquiv

variable (D) in
/-- The product of the groups GL_l(𝔽_w) over the chosen places w above p₀ and p₁ has order
∏_i |GL_l(𝔽_{p_i})|^f, where p_i = `D.levelPrime i` and f is the number of infinite places of E:
there are f chosen places above each p_i. -/
lemma card_pi_GL_chosenPlace (l : ℕ) :
    Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL (Fin l) (ResField (D.chosenPlace x))) =
      ∏ i : Fin 2, Nat.card (GL (Fin l) (ZMod (D.levelPrime i))) ^ D.f :=
  calc Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL (Fin l) (ResField (D.chosenPlace x)))
      = ∏ i : Fin 2, ∏ w : D.ChosenPlace i, Nat.card (GL (Fin l) (ResField w.val)) :=
        Nat.card_pi.trans (Fintype.prod_sigma _)
    _ = ∏ i : Fin 2, Nat.card (GL (Fin l) (ZMod (D.levelPrime i))) ^ D.f := by
        simp only [card_GL_resField_eq_card_GL_zmod, prod_const, card_univ, card_chosenPlace]

/-! ### The principal level and the orders of stabilisers -/

/-- The elements of the finite adelic unitary group on the index set `n` that are integral and
reduce to `1` at every chosen place, that is, at every prime divisor of `D.piM`. -/
abbrev chosenLevel : Subgroup (Gf D.E n) := levelOf (n := n) D.chosenPlace ⊥

variable {K : Subgroup (Gf D.E n)}

/-- Of a place `w` above the prime `D.levelPrime i` and its conjugate, exactly one is chosen. -/
lemma isChosen_star_iff {i : Fin 2} {w : FinPlace D.E} (hw : ↑(D.levelPrime i) ∈ w.asIdeal) :
    D.IsChosen (star w) ↔ ¬D.IsChosen w := by
  obtain ⟨c, h_norm, h_coprime⟩ := D.exists_piM_mul_star_eq_levelPrime_mul_coprime (i := i)
  exact star_mem_iff_notMem (levelPrime_modEq_one D i) hw h_norm h_coprime

/-- For a finite index type `n` with at most `D.r * D.t` elements, the order of the product of the
groups `GL n (ResField w)`, over the chosen places w above `D.levelPrime 0` and `D.levelPrime 1`,
divides `D.chosenGroupOrder`. -/
lemma card_GL_dvd_chosenGroupOrder (hn : Fintype.card n ≤ D.r * D.t) :
    Nat.card (∀ x : (i : Fin 2) × D.ChosenPlace i, GL n (ResField (D.chosenPlace x))) ∣
      D.chosenGroupOrder := by
  -- `g ↦ diag (g, 1)` embeds `GL n` in `GL (Fin (r * t))` at every chosen place.
  obtain ⟨u⟩ : Nonempty (n ↪ Fin (D.r * D.t)) := nonempty_of_card_le (by simpa)
  exact card_dvd_of_injective (.piMap fun _ ↦ extendGL u) (.piMap fun _ ↦ extendGL_injective u)

/-- The chosen places, indexed by the pairs (i, w) with w a chosen place above p_i, are pairwise
distinct, and none is the conjugate of one of them. -/
instance isConjApart_chosenPlace : IsConjApart D.chosenPlace where
  injective := by
    -- The norm of a chosen place above p_i is p_i, so the place determines `i`.
    rintro ⟨i, w, hw, hw_mem⟩ ⟨i', w', hw', hw'_mem⟩ (rfl : w = w')
    obtain rfl : i = i' :=
      D.levelPrime_injective ((D.q_eq_levelPrime hw_mem).symm.trans (D.q_eq_levelPrime hw'_mem))
    rfl
  star_ne := by
    -- The conjugate of a chosen place is not chosen.
    rintro ⟨i, w, hw, hw_mem⟩ ⟨i', w', hw', hw'_mem⟩ (rfl : star w = w')
    exact (D.isChosen_star_iff hw_mem).1 hw' hw

/-- The places `D.chosenPlace x`, for x = (i, w) with w a chosen place above p_i, are exactly the
chosen places. -/
lemma range_chosenPlace : Set.range D.chosenPlace = {w : FinPlace D.E | D.IsChosen w} := by
  ext w
  rw [Set.mem_ofPred, isChosen_iff]
  refine ⟨?_, fun ⟨i, hw⟩ ↦ ⟨⟨i, w, hw⟩, rfl⟩⟩
  rintro ⟨⟨i, w, hw⟩, rfl⟩
  exact ⟨i, hw⟩

/-- If `D.piM`, whose prime divisors are the chosen places, divides the integer `a` of E, the
principal congruence subgroup of level `a` is contained in `New.Data.chosenLevel`. -/
lemma principalLevel_le_chosenLevel {a : NumberField.RingOfIntegers D.E} (ha : D.piM ∣ a) :
    principalLevel n a ≤ D.chosenLevel :=
  principalLevel_le_levelOf fun ⟨_, w, hw, _⟩ ↦ Ideal.mem_of_dvd w.asIdeal ha hw

/-- Let K be a subgroup of the integral points of the finite adelic unitary group on `n` whose
elements reduce to `1` at the chosen places above the prime `D.levelPrime i`. If `n` has at most
`4 * D.n D.m` elements, four times the rank of the last stage, the stabiliser of each coset gK in
the rational unitary group is trivial. -/
theorem classAut_eq_bot_of_le_levelOf_chosenPlace (i : Fin 2)
    (hK : K ≤ levelOf (n := n) (fun w : D.ChosenPlace i ↦ w.1) ⊥)
    (hn : Fintype.card n ≤ 4 * D.n D.m) (g : Gf D.E n) : classAut stdRatPoints K g = ⊥ := by
  -- `Variety.classAut_eq_bot` asks that the norms of the places multiply to more than
  -- `(2 * card n) ^ [E : ℚ]`. The `f` places have norm p_i, and `[E : ℚ] = 2 * f`.
  have h_size : (2 * (4 * D.n D.m)) ^ 2 < D.levelPrime i := D.nat_lt_of_hasLogBound
  refine Variety.classAut_eq_bot Subtype.val_injective ?_ hK g
  calc (2 * Fintype.card n) ^ Module.finrank ℚ D.E
      ≤ ((2 * (4 * D.n D.m)) ^ 2) ^ D.f := by
        rw [finrank_eq_two_mul_card_infinitePlace, pow_mul]
        gcongr
    _ < D.levelPrime i ^ D.f := by gcongr
    _ = ∏ w : D.ChosenPlace i, w.val.q := by
        simp [fun w : D.ChosenPlace i ↦ D.q_eq_levelPrime w.property.right, D.card_chosenPlace]

/-- If n has at most `2 * D.n D.m` elements, every subgroup K of `New.Data.chosenLevel` is
sufficiently small: the stabiliser of each point gK in the rational unitary group is trivial. -/
lemma classAut_eq_bot_of_le_chosenLevel (hK : K ≤ D.chosenLevel)
    (hn : Fintype.card n ≤ 2 * D.n D.m) : ∀ g : Gf D.E n, classAut stdRatPoints K g = ⊥ := by
  have h_le : D.chosenLevel ≤ levelOf (n := n) (fun w : D.ChosenPlace 0 ↦ w.1) ⊥ := by
    intro k hk
    obtain ⟨hk_int, hk_red⟩ := mem_levelOf.1 hk
    exact mem_levelOf.2 ⟨hk_int, mem_bot.2 (funext fun w ↦ congrFun (mem_bot.1 hk_red) ⟨0, w⟩)⟩
  exact D.classAut_eq_bot_of_le_levelOf_chosenPlace 0 (hK.trans h_le) (by lia)

/-- For the standard definite hermitian space on an index set `n` with at most `2 * D.n D.m`
elements, a subgroup K of the stabiliser of the standard lattice and any finite adelic g, the
stabiliser of gK in the rational unitary group has order dividing `New.Data.chosenGroupOrder`.

A consequence of a unitary variant of Minkowski's lemma on integral matrices of finite order. -/
lemma card_classAut_dvd_chosenGroupOrder (hn : Fintype.card n ≤ 2 * D.n D.m)
    (hK : K ≤ stdLevel D.E n) (g : Gf D.E n) :
    Nat.card (classAut stdRatPoints K g) ∣ D.chosenGroupOrder := by
  -- Conjugate by `g⁻¹` into `K ≤ stdLevel`, then reduce at the chosen places.
  let conj : Gf D.E n →* Gf D.E n := (MulAut.conj g⁻¹).toMonoidHom
  have h_le : classAut stdRatPoints K g ≤ (stdLevel D.E n).comap conj :=
    inf_le_right.trans (comap_mono hK)
  let red : classAut stdRatPoints K g →*
      ∀ x : (i : Fin 2) × D.ChosenPlace i, GL n (ResField (D.chosenPlace x)) :=
    (stdLevel.reduceFamily D.chosenPlace).comp
      ((conj.subgroupComap (stdLevel D.E n)).comp (inclusion h_le))
  -- The kernel lies in the stabiliser for `D.chosenLevel`, which is trivial.
  have h_inj : Injective red := (injective_iff_map_eq_one red).2 fun ⟨γ, hγ_rat, hγ_K⟩ h_red ↦ by
    have h_mem : γ ∈ classAut stdRatPoints D.chosenLevel g :=
      ⟨hγ_rat, mem_levelOf.2 ⟨hK hγ_K, h_red⟩⟩
    exact Subtype.ext (by simpa [D.classAut_eq_bot_of_le_chosenLevel le_rfl hn g] using h_mem)
  have h_rank : 2 * D.n D.m ≤ D.r * D.t := D.nat_le_of_hasLogBound
  exact (card_dvd_of_injective _ h_inj).trans (D.card_GL_dvd_chosenGroupOrder (hn.trans h_rank))

/-! ### The residue characters, and size bounds -/

lemma IsChosen.not_star (hw : D.IsChosen w) : ¬D.IsChosen (star w) := by
  obtain ⟨i, -, hw_mem⟩ := D.isChosen_iff.1 hw
  exact fun hw_star ↦ (isChosen_star_iff hw_mem).1 hw_star hw

/-- The character `D.chiMLocal w` of the residue field at `w` is trivial unless `w` is chosen, and
then it has order `P.q₂ D.towerExp = (P.q₀ * P.d) ^ (D.towerExp + 6)`, which exceeds `8 * D.m`. For
an integer `n` with `n ≠ 0` and `|n| ≤ 8 * D.m`, where `D.m` is the number of lifts, its `n`-th
power is nontrivial exactly when `w` is chosen. -/
lemma chiMLocal_zpow_ne_one_iff_isChosen (n : ℤ) (hn_ne : n ≠ 0) (hn_le : n.natAbs ≤ 8 * D.m)
    (w : FinPlace D.E) : (D.chiMLocal ^ n) w ≠ 1 ↔ D.IsChosen w := by
  by_cases hw : D.IsChosen w
  · -- `D.chiMLocal w` has order `q₂`, a multiple of `q₁ d > 8 m ≥ |n|`.
    have h_size : 8 * D.m < P.q₁ D.towerExp * P.d := D.nat_lt_of_hasLogBound
    have h_not : ¬P.q₂ D.towerExp ∣ n.natAbs := fun h_dvd ↦
      Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.2 hn_ne) (hn_le.trans_lt h_size)
        (q₁_mul_d_dvd_q₂.trans h_dvd)
    have h_ne : D.chiMLocal w ^ n ≠ 1 := by
      rwa [Ne, ← orderOf_dvd_iff_zpow_eq_one, D.orderOf_chiMLocal hw, Int.natCast_dvd]
    exact iff_of_true h_ne hw
  · simp [hw]

/-- The number `q₂ = (q₀ d) ^ (s + 6)` with `s = D.towerExp`, which is the order of the residue
characters `D.chiMLocal w` at the chosen places, is at most `exp (log b / 9)`, where
`log b = D.logB`. -/
instance : D.HasLogUpper (P.q₂ D.towerExp) (D.logB / 9) := by
  -- `q₂` is at most a fixed power of `x`, and `log x ≤ log x₁` is negligible against `log b`.
  have h_scale : D.logX ≤ D.logX₁ := by grind [D.scale_inequalities]
  have h_pow : D.x ^ (33 * (P.q₀ * P.d)) ≤ exp (D.logB / 9) := by
    rw [← exp_nat_mul, exp_le_exp]
    calc _ ≤ (33 * (P.q₀ * P.d) : ℕ) * D.logX₁ := by gcongr
      _ ≤ D.logB / 9 := D.le_of_hasLogBound
  exact hasLogUpper_of_le_of_nonneg (D.q₂_le.trans h_pow) (Nat.cast_nonneg _)

variable (D) in
/-- The logarithm of `D.chosenGroupOrder` is at most `D.x ^ 32`, where `D.x = exp D.logX` is a scale
of the data `D`. -/
lemma log_chosenGroupOrder_le : log D.chosenGroupOrder ≤ D.x ^ 32 := by
  -- `GL n` over a field with `q` elements has at most `q ^ n²` elements.
  have h_order : D.chosenGroupOrder ≤ D.M ^ ((D.r * D.t) ^ 2 * D.f) :=
    calc _ = ∏ i : Fin 2, Nat.card (GL (Fin (D.r * D.t)) (ZMod (D.levelPrime i))) ^ D.f :=
          D.card_pi_GL_chosenPlace (D.r * D.t)
      _ ≤ ∏ i : Fin 2, (D.levelPrime i ^ (D.r * D.t) ^ 2) ^ D.f := by
          gcongr with i
          simpa using card_GL_le (n := Fin (D.r * D.t)) (ZMod (D.levelPrime i))
      _ = D.M ^ ((D.r * D.t) ^ 2 * D.f) := by
          simp only [← pow_mul, Fin.prod_univ_two, Data.M, mul_pow (D.levelPrime 0)]
  calc log D.chosenGroupOrder ≤ log (D.M ^ ((D.r * D.t) ^ 2 * D.f) : ℕ) :=
        log_le_log (Nat.cast_pos.2 (NeZero.pos _)) (Nat.cast_le.2 h_order)
    _ = (D.r * D.t) ^ 2 * D.f * log D.M := by simp
    _ ≤ exp (32 * D.logX) := D.le_of_hasLogBound
    _ = D.x ^ 32 := exp_nat_mul D.logX 32

/-- The bound `log chosenGroupOrder ≤ D.x ^ 32 = exp (32 * D.logX)`, as a logarithmic upper
bound. -/
instance : D.HasLogUpper (log D.chosenGroupOrder) (32 * D.logX) :=
  hasLogUpper_of_le_of_nonneg D.log_chosenGroupOrder_le (log_natCast_nonneg _)

end New.Data

end
