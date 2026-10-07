import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Lie.IdealOperations
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Pi
import OAI.Combinatorics.Progressions.Estimates.DilationPairFiltration
import OAI.Combinatorics.Progressions.Estimates.LieFiniteProduct
import OAI.Combinatorics.Progressions.Nilpotent.SquarefreeBracketCoefficients
import OAI.Combinatorics.Progressions.Polynomial.SquarefreeBlockDegree

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable (σ L : Type*) [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

structure MultidegreeLieFiltration (s : ℕ) (bound : σ → ℕ) where
  ordinary : NilpotentLieFiltration L s
  layer : (σ → ℕ) → Submodule ℚ L
  antitone : Antitone layer
  zero_eq_top : layer 0 = ⊤
  lie_mem : ∀ {a b : σ → ℕ} {x y : L}, x ∈ layer a → y ∈ layer b → ⁅x, y⁆ ∈ layer (a + b)
  terminal : ∀ a, ¬a ≤ bound → layer a = ⊥
  degree_eq : ∀ n, ordinary.layer n = ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), layer a

namespace MultidegreeLieFiltration

variable {σ L} {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def layerIdeal (a : σ → ℕ) : LieIdeal ℚ L :=
  { F.layer a with
    lie_mem := by
      intro x y hy
      change ⁅x, y⁆ ∈ F.layer a
      have hx : x ∈ F.layer 0 := by simp only [F.zero_eq_top, Submodule.mem_top]
      simpa only [zero_add] using F.lie_mem hx hy }

@[simp] theorem mem_layerIdeal (a : σ → ℕ) (x : L) :
    x ∈ F.layerIdeal a ↔ x ∈ F.layer a := Iff.rfl

theorem layer_le_ordinary (a : σ → ℕ) : F.layer a ≤ F.ordinary.layer (∑ i, a i) := by
  rw [F.degree_eq]
  exact le_iSup_of_le a (le_iSup_of_le le_rfl le_rfl)

abbrev Group := F.ordinary.Group

def subgroup (a : σ → ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal a).toLieSubalgebra

@[simp] theorem mem_subgroup (a : σ → ℕ) (x : F.Group) :
    x ∈ F.subgroup a ↔ x.coord ∈ F.layer a := Iff.rfl

theorem subgroup_normal (a : σ → ℕ) : (F.subgroup a).Normal :=
  NilpotentLieBCHGroup.subgroup_ideal_normal (F.layerIdeal a)

theorem subgroup_antitone : Antitone F.subgroup := fun _ _ h _ hx => F.antitone h hx

theorem subgroup_le_ordinary (a : σ → ℕ) : F.subgroup a ≤ F.ordinary.subgroup (∑ i, a i) :=
  fun _ hx => F.layer_le_ordinary a hx

theorem subgroup_commutator_mem {a b : σ → ℕ} {x y : F.Group}
    (hx : x ∈ F.subgroup a) (hy : y ∈ F.subgroup b) :
    x * y * x⁻¹ * y⁻¹ ∈ F.subgroup (a + b) :=
  NilpotentLieBCHGroup.commutator_mem_ideal (F.layerIdeal (a + b)) x y (F.lie_mem hx hy)

theorem subgroup_eq_bot {a : σ → ℕ} (ha : ¬a ≤ bound) : F.subgroup a = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply NilpotentLieBCHGroup.ext
  change x.coord = 0
  have h := (F.mem_subgroup a x).mp hx
  simpa only [F.terminal a ha, Submodule.mem_bot] using h

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def multidegreeTotalLayer (P : (σ → ℕ) → Submodule ℚ L) (n : ℕ) : Submodule ℚ L :=
  ⨆ a : {a : σ → ℕ // n ≤ ∑ i, a i}, P a.val

theorem layer_le_multidegreeTotalLayer (P : (σ → ℕ) → Submodule ℚ L) (a : σ → ℕ) (n : ℕ)
    (ha : n ≤ ∑ i, a i) : P a ≤ multidegreeTotalLayer P n :=
  le_iSup (fun b : {b : σ → ℕ // n ≤ ∑ i, b i} => P b.val) ⟨a, ha⟩

theorem multidegreeTotalLayer_antitone (P : (σ → ℕ) → Submodule ℚ L) :
    Antitone (multidegreeTotalLayer P) := by
  intro i j hij
  apply iSup_le
  intro a
  exact layer_le_multidegreeTotalLayer P a.val i (hij.trans a.property)

theorem multidegreeTotalLayer_eq (P : (σ → ℕ) → Submodule ℚ L) (n : ℕ) :
    multidegreeTotalLayer P n = ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), P a := by
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup_of_le a.val (le_iSup_of_le a.property le_rfl)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    exact layer_le_multidegreeTotalLayer P a n ha

theorem multidegreeTotalLayer_lie_mem (P : (σ → ℕ) → Submodule ℚ L)
    (hP : ∀ {a b : σ → ℕ} {x y : L}, x ∈ P a → y ∈ P b → ⁅x, y⁆ ∈ P (a + b))
    {i j : ℕ} {x y : L} (hx : x ∈ multidegreeTotalLayer P i) (hy : y ∈ multidegreeTotalLayer P j) :
    ⁅x, y⁆ ∈ multidegreeTotalLayer P (i + j) := by
  refine Submodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ multidegreeTotalLayer P (i + j)) ?_ ?_ ?_
  · intro a u hu
    refine Submodule.iSup_induction _ hy
      (motive := fun z => ⁅u, z⁆ ∈ multidegreeTotalLayer P (i + j)) ?_ ?_ ?_
    · intro b v hv
      apply layer_le_multidegreeTotalLayer P (a.val + b.val) (i + j) _ (hP hu hv)
      simpa only [Pi.add_apply, Finset.sum_add_distrib] using Nat.add_le_add a.property b.property
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro u v hu hv
      rw [lie_add]
      exact Submodule.add_mem _ hu hv
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro u v hu hv
    rw [add_lie]
    exact Submodule.add_mem _ hu hv

theorem multidegreeTotalLayer_terminal (P : (σ → ℕ) → Submodule ℚ L) (bound : σ → ℕ)
    (hP : ∀ a, ¬a ≤ bound → P a = ⊥) (s : ℕ) (hs : (∑ i, bound i) ≤ s) :
    multidegreeTotalLayer P (s + 1) = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro a
  have ha : ¬a.val ≤ bound := by
    intro h
    have hsum : (∑ i, a.val i) ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => h i)
    have hn := a.property
    omega
  rw [hP a.val ha]

noncomputable def MultidegreeLieFiltration.ofLayers
    (P : (σ → ℕ) → Submodule ℚ L) (hmono : Antitone P) (hzero : P 0 = ⊤)
    (hlie : ∀ {a b : σ → ℕ} {x y : L}, x ∈ P a → y ∈ P b → ⁅x, y⁆ ∈ P (a + b))
    (hpositive : multidegreeTotalLayer P 1 = ⊤)
    (bound : σ → ℕ) (hterminal : ∀ a, ¬a ≤ bound → P a = ⊥)
    (s : ℕ) (hs : (∑ i, bound i) ≤ s) : MultidegreeLieFiltration σ L s bound where
  ordinary :=
    { layer := multidegreeTotalLayer P
      antitone := multidegreeTotalLayer_antitone P
      one_eq_top := hpositive
      lie_mem := multidegreeTotalLayer_lie_mem P hlie
      terminal := multidegreeTotalLayer_terminal P bound hterminal s hs }
  layer := P
  antitone := hmono
  zero_eq_top := hzero
  lie_mem := hlie
  terminal := hterminal
  degree_eq := multidegreeTotalLayer_eq P

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem multidegree_sum_lt_of_lt {σ : Type*} [Fintype σ] {a b : σ → ℕ} (hab : a < b) :
    (∑ i, a i) < ∑ i, b i := by
  obtain ⟨i, hi⟩ := not_forall.mp hab.not_ge
  exact Finset.sum_lt_sum (fun j _ => hab.le j)
    ⟨i, Finset.mem_univ i, Nat.lt_of_not_ge hi⟩

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def strictUpperLayer (a : σ → ℕ) : LieIdeal ℚ L :=
  ⨆ i : σ, F.layerIdeal (a + Pi.single i 1)

theorem successor_le_strictUpperLayer (a : σ → ℕ) (i : σ) :
    F.layerIdeal (a + Pi.single i 1) ≤ F.strictUpperLayer a :=
  le_iSup (fun j => F.layerIdeal (a + Pi.single j 1)) i

theorem strictUpperLayer_le_layer (a : σ → ℕ) :
    F.strictUpperLayer a ≤ F.layerIdeal a := by
  apply iSup_le
  intro i
  exact F.antitone (fun j => Nat.le_add_right (a j) _)

theorem strictUpperLayer_antitone : Antitone F.strictUpperLayer := by
  intro a b hab
  apply iSup_le
  intro i
  exact (F.antitone (fun j => Nat.add_le_add_right (hab j) _)).trans
    (F.successor_le_strictUpperLayer a i)

theorem layer_le_strictUpperLayer {a b : σ → ℕ} (hab : a < b) :
    F.layerIdeal b ≤ F.strictUpperLayer a := by
  obtain ⟨i, hi⟩ := not_forall.mp hab.not_ge
  have hstep : a + Pi.single i 1 ≤ b := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Pi.add_apply, Pi.single_eq_same] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    · simpa only [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero] using hab.le j
  exact (F.antitone hstep).trans (F.successor_le_strictUpperLayer a i)

theorem strictUpperLayer_le_ordinary (a : σ → ℕ) :
    (F.strictUpperLayer a).toSubmodule ≤ F.ordinary.layer ((∑ i, a i) + 1) := by
  rw [strictUpperLayer, LieSubmodule.iSup_toSubmodule]
  apply iSup_le
  intro i
  change F.layer (a + Pi.single i 1) ≤ _
  have hsum : (∑ j, (a + Pi.single i 1 : σ → ℕ) j) = (∑ j, a j) + 1 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    congr 1
    simp
  rw [← hsum]
  exact F.layer_le_ordinary (a + Pi.single i 1)

theorem strictUpperLayer_top : F.strictUpperLayer bound = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro i
  have hnot : ¬bound + Pi.single i 1 ≤ bound := by
    intro h
    have hh := h i
    simp only [Pi.add_apply, Pi.single_eq_same] at hh
    omega
  intro x hx
  change x = 0
  have h : x ∈ F.layer (bound + Pi.single i 1) := hx
  simpa only [F.terminal _ hnot, Submodule.mem_bot] using h

theorem strictUpper_lie_layer {a b : σ → ℕ} {x y : L}
    (hx : x ∈ F.strictUpperLayer a) (hy : y ∈ F.layer b) :
    ⁅x, y⁆ ∈ F.strictUpperLayer (a + b) := by
  change x ∈ ⨆ i : σ, F.layerIdeal (a + Pi.single i 1) at hx
  refine LieSubmodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ F.strictUpperLayer (a + b)) ?_ ?_ ?_
  · intro i u hu
    apply F.successor_le_strictUpperLayer (a + b) i
    change ⁅u, y⁆ ∈ F.layer (a + b + Pi.single i 1)
    simpa only [add_right_comm a (Pi.single i 1) b] using F.lie_mem hu hy
  · simpa only [zero_lie] using (F.strictUpperLayer (a + b)).zero_mem
  · intro u v hu hv
    rw [LieRing.add_lie]
    exact (F.strictUpperLayer (a + b)).add_mem hu hv

theorem layer_lie_strictUpper {a b : σ → ℕ} {x y : L}
    (hx : x ∈ F.layer a) (hy : y ∈ F.strictUpperLayer b) :
    ⁅x, y⁆ ∈ F.strictUpperLayer (a + b) := by
  have h := (F.strictUpperLayer (b + a)).neg_mem (F.strictUpper_lie_layer hy hx)
  change ⁅x, y⁆ ∈ (F.strictUpperLayer (a + b)).toSubmodule
  simpa only [lie_skew, add_comm b a] using h

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def multidegreeWeight {σ : Type*} [Fintype σ] (c a : σ → ℕ) : ℕ := ∑ i, c i * a i

theorem multidegreeWeight_add {σ : Type*} [Fintype σ] (c a b : σ → ℕ) :
    multidegreeWeight c (a + b) = multidegreeWeight c a + multidegreeWeight c b := by
  simp only [multidegreeWeight, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem multidegreeWeight_mono {σ : Type*} [Fintype σ] (c : σ → ℕ) {a b : σ → ℕ}
    (hab : a ≤ b) : multidegreeWeight c a ≤ multidegreeWeight c b :=
  Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (c i) (hab i))

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedLayer (c : σ → ℕ) (n : ℕ) : LieIdeal ℚ L :=
  ⨆ a : {a : σ → ℕ // n ≤ multidegreeWeight c a}, F.layerIdeal a.val

theorem layer_le_weightedLayer (c a : σ → ℕ) (n : ℕ) (ha : n ≤ multidegreeWeight c a) :
    F.layerIdeal a ≤ F.weightedLayer c n :=
  le_iSup (fun b : {b : σ → ℕ // n ≤ multidegreeWeight c b} => F.layerIdeal b.val) ⟨a, ha⟩

theorem weightedLayer_antitone (c : σ → ℕ) : Antitone (F.weightedLayer c) := by
  intro m n hmn
  apply iSup_le
  intro a
  exact F.layer_le_weightedLayer c a.val m (hmn.trans a.property)

theorem weightedLayer_zero (c : σ → ℕ) : F.weightedLayer c 0 = ⊤ := by
  apply top_unique
  intro x _
  apply F.layer_le_weightedLayer c 0 0 (Nat.zero_le _)
  change x ∈ F.layer 0
  simp only [F.zero_eq_top, Submodule.mem_top]

theorem weightedLayer_terminal (c : σ → ℕ) :
    F.weightedLayer c (multidegreeWeight c bound + 1) = ⊥ := by
  apply bot_unique
  apply iSup_le
  intro a
  have hnot : ¬a.val ≤ bound := by
    intro ha
    have h := (multidegreeWeight_mono c ha)
    have h' := a.property
    omega
  intro x hx
  change x = 0
  have h : x ∈ F.layer a.val := hx
  simpa only [F.terminal a.val hnot, Submodule.mem_bot] using h

theorem weightedLayer_lie_mem (c : σ → ℕ) {i j : ℕ} {x y : L}
    (hx : x ∈ F.weightedLayer c i) (hy : y ∈ F.weightedLayer c j) :
    ⁅x, y⁆ ∈ F.weightedLayer c (i + j) := by
  change x ∈ ⨆ a : {a : σ → ℕ // i ≤ multidegreeWeight c a}, F.layerIdeal a.val at hx
  refine LieSubmodule.iSup_induction _ hx
    (motive := fun z => ⁅z, y⁆ ∈ F.weightedLayer c (i + j)) ?_ ?_ ?_
  · intro a u hu
    change y ∈ ⨆ b : {b : σ → ℕ // j ≤ multidegreeWeight c b}, F.layerIdeal b.val at hy
    refine LieSubmodule.iSup_induction _ hy
      (motive := fun z => ⁅u, z⁆ ∈ F.weightedLayer c (i + j)) ?_ ?_ ?_
    · intro b v hv
      apply F.layer_le_weightedLayer c (a.val + b.val) (i + j)
        (by rw [multidegreeWeight_add]; exact Nat.add_le_add a.property b.property)
      exact F.lie_mem hu hv
    · simpa only [lie_zero] using (F.weightedLayer c (i + j)).zero_mem
    · intro v z hv hz
      rw [LieRing.lie_add]
      exact (F.weightedLayer c (i + j)).add_mem hv hz
  · simpa only [zero_lie] using (F.weightedLayer c (i + j)).zero_mem
  · intro u v hu hv
    rw [LieRing.add_lie]
    exact (F.weightedLayer c (i + j)).add_mem hu hv

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}

theorem pi_degree_eq (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) (n : ℕ) :
    Submodule.pi Set.univ (fun i => (F i).ordinary.layer n) =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ j, a j), Submodule.pi Set.univ (fun i => (F i).layer a) := by
  classical
  apply le_antisymm
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [(F i).degree_eq]
    simp only [Submodule.map_iSup]
    refine iSup_le fun a => iSup_le fun ha => ?_
    apply le_trans (Submodule.map_le_iff_le_comap.mpr
      (Submodule.le_comap_single_pi (fun i => (F i).layer a)))
    exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)
  · refine iSup_le fun a => iSup_le fun ha => ?_
    exact Submodule.pi_mono fun i _ => ((F i).layer_le_ordinary a).trans ((F i).ordinary.antitone ha)

noncomputable def pi (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) :
    MultidegreeLieFiltration σ (∀ i, L i) s bound where
  ordinary := NilpotentLieFiltration.pi (fun i => (F i).ordinary)
  layer a := Submodule.pi Set.univ (fun i => (F i).layer a)
  antitone _ _ h := Submodule.pi_mono (fun i _ => (F i).antitone h)
  zero_eq_top := by simp only [zero_eq_top, Submodule.pi_top]
  lie_mem hx hy i hi := (F i).lie_mem (hx i hi) (hy i hi)
  terminal a ha := by
    simp only [show ∀ i, (F i).layer a = ⊥ from fun i => (F i).terminal a ha, Submodule.pi_univ_bot]
  degree_eq := pi_degree_eq F

@[simp] theorem mem_pi_layer (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)
    (a : σ → ℕ) (x : ∀ i, L i) :
    x ∈ (pi F).layer a ↔ ∀ i, x i ∈ (F i).layer a := by
  simp only [pi, Submodule.mem_pi, Set.mem_univ, forall_true_left]

def piLayerEquiv (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) (a : σ → ℕ) :
    (∀ i, (F i).layer a) ≃ₗ[ℚ] (pi F).layer a where
  toFun x := ⟨fun i => x i, (mem_pi_layer F a _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F a _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeAdaptedModule : Submodule ℚ (SquarefreePolynomial ι L) where
  carrier := {x | ∀ a : SquarefreeIndex ι,
    squarefreePolynomialEquiv x a ∈ F.layer (blockDegree π a.val) ∧
      (a.val = 0 → squarefreePolynomialEquiv x a = 0)}
  zero_mem' := by
    intro a
    simp only [map_zero, Pi.zero_apply]
    exact ⟨(F.layer _).zero_mem, fun _ => True.intro⟩
  add_mem' := by
    intro x y hx hy a
    simp only [map_add, Pi.add_apply]
    exact ⟨(F.layer _).add_mem (hx a).1 (hy a).1,
      fun ha => by rw [(hx a).2 ha, (hy a).2 ha, add_zero]⟩
  smul_mem' := by
    intro r x hx a
    simp only [map_smul, Pi.smul_apply]
    exact ⟨(F.layer _).smul_mem r (hx a).1,
      fun ha => by rw [(hx a).2 ha, smul_zero]⟩

theorem mem_squarefreeAdaptedModule (x : SquarefreePolynomial ι L) :
    x ∈ F.squarefreeAdaptedModule π ↔ ∀ a : SquarefreeIndex ι,
      squarefreePolynomialEquiv x a ∈ F.layer (blockDegree π a.val) ∧
        (a.val = 0 → squarefreePolynomialEquiv x a = 0) := Iff.rfl

theorem squarefreeMonomial_mem_adapted (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : L) (hv : v ∈ F.layer (blockDegree π a.val)) :
    squarefreeMonomial a v ∈ F.squarefreeAdaptedModule π := by
  intro b
  by_cases hab : a = b
  · subst b
    rw [squarefreePolynomialEquiv_monomial_self]
    exact ⟨hv, fun he => False.elim (ha he)⟩
  · rw [squarefreePolynomialEquiv_monomial_ne a b hab v]
    exact ⟨(F.layer _).zero_mem, fun _ => rfl⟩

theorem squarefreeMonomial_component_mem (x : SquarefreePolynomial ι L)
    (hx : x ∈ F.squarefreeAdaptedModule π) (a : SquarefreeIndex ι) :
    squarefreeMonomial a (squarefreePolynomialEquiv x a) ∈ F.squarefreeAdaptedModule π := by
  by_cases ha : a.val = 0
  · rw [(hx a).2 ha, map_zero]
    exact (F.squarefreeAdaptedModule π).zero_mem
  · exact F.squarefreeMonomial_mem_adapted π a ha _ (hx a).1

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairLayer (q : ℚ) (a : σ → ℕ) : Submodule ℚ (L × L) :=
  scaledPairLayer (F.layer a) (F.strictUpperLayer a).toSubmodule (q ^ ∑ i, a i)

theorem mem_dilationPairLayer (q : ℚ) (a : σ → ℕ) (x : L × L) :
    x ∈ F.dilationPairLayer q a ↔ x.1 ∈ F.layer a ∧ x.2 ∈ F.layer a ∧
      x.1 - q ^ (∑ i, a i) • x.2 ∈ F.strictUpperLayer a := Iff.rfl

theorem dilationPairLayer_antitone (q : ℚ) : Antitone (F.dilationPairLayer q) := by
  intro a b hab x hx
  by_cases heq : a = b
  · subst b
    exact hx
  have hlt : a < b := lt_iff_le_not_ge.mpr ⟨hab, fun hba => heq (le_antisymm hab hba)⟩
  refine ⟨F.antitone hab hx.1, F.antitone hab hx.2.1, ?_⟩
  change x.1 - q ^ (∑ i, a i) • x.2 ∈ F.strictUpperLayer a
  have hdiff : x.1 - q ^ (∑ i, a i) • x.2 =
      (x.1 - q ^ (∑ i, b i) • x.2) + (q ^ (∑ i, b i) - q ^ (∑ i, a i)) • x.2 := by
    rw [sub_smul]
    abel
  rw [hdiff]
  exact (F.strictUpperLayer a).add_mem (F.strictUpperLayer_antitone hab hx.2.2)
    ((F.strictUpperLayer a).smul_mem _ (F.layer_le_strictUpperLayer hlt hx.2.1))

theorem dilationPairLayer_lie_mem (q : ℚ) {a b : σ → ℕ} {x y : L × L}
    (hx : x ∈ F.dilationPairLayer q a) (hy : y ∈ F.dilationPairLayer q b) :
    ⁅x, y⁆ ∈ F.dilationPairLayer q (a + b) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - q ^ (∑ i, (a + b) i) • ⁅x.2, y.2⁆ ∈ F.strictUpperLayer (a + b)
  have hdiff : ⁅x.1, y.1⁆ - q ^ (∑ i, (a + b) i) • ⁅x.2, y.2⁆ =
      ⁅x.1 - q ^ (∑ i, a i) • x.2, y.1⁆ +
        q ^ (∑ i, a i) • ⁅x.2, y.1 - q ^ (∑ i, b i) • y.2⁆ := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, sub_lie, lie_sub,
      smul_lie, lie_smul, smul_sub, smul_smul, pow_add]
    abel
  rw [hdiff]
  have h₁ := F.strictUpper_lie_layer hx.2.2 hy.1
  have h₂ := F.layer_lie_strictUpper hx.2.1 hy.2.2
  rw [scaledPairDifference_apply] at h₁ h₂
  exact (F.strictUpperLayer (a + b)).add_mem h₁ ((F.strictUpperLayer (a + b)).smul_mem _ h₂)

theorem dilationPairLayer_le_ordinary (q : ℚ) (a : σ → ℕ) :
    F.dilationPairLayer q a ≤ F.ordinary.dilationPairLayer q (∑ i, a i) := by
  intro x hx
  exact ⟨F.layer_le_ordinary a hx.1, F.layer_le_ordinary a hx.2.1,
    F.strictUpperLayer_le_ordinary a hx.2.2⟩

theorem dilationPairLayer_le_subalgebra (q : ℚ) (a : σ → ℕ) (ha : 1 ≤ ∑ i, a i) :
    F.dilationPairLayer q a ≤ (F.ordinary.dilationPairSubalgebra q).toSubmodule :=
  (F.dilationPairLayer_le_ordinary q a).trans (F.ordinary.dilationPairLayer_antitone q ha)

theorem dilationPairLayer_terminal (q : ℚ) (a : σ → ℕ) (ha : ¬a ≤ bound) :
    F.dilationPairLayer q a = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Prod.ext
  · exact (Submodule.mem_bot ℚ).mp (F.terminal a ha ▸ hx.1)
  · exact (Submodule.mem_bot ℚ).mp (F.terminal a ha ▸ hx.2.1)

theorem dilationPairLayer_top_relation (q : ℚ) {x : L × L}
    (hx : x ∈ F.dilationPairLayer q bound) : x.1 = q ^ (∑ i, bound i) • x.2 := by
  have h : x.1 - q ^ (∑ i, bound i) • x.2 ∈ F.strictUpperLayer bound := hx.2.2
  rw [F.strictUpperLayer_top, LieSubmodule.mem_bot, sub_eq_zero] at h
  exact h

theorem dilationPairLayer_diagonal (q : ℚ) (a : σ → ℕ) {x : L} (hx : x ∈ F.layer a) :
    (q ^ (∑ i, a i) • x, x) ∈ F.dilationPairLayer q a :=
  ⟨(F.layer a).smul_mem _ hx, hx, by simp⟩

theorem dilationPairLayer_of_strictUpper (q : ℚ) (a : σ → ℕ) {x y : L}
    (hx : x ∈ F.strictUpperLayer a) (hy : y ∈ F.strictUpperLayer a) :
    (x, y) ∈ F.dilationPairLayer q a :=
  ⟨F.strictUpperLayer_le_layer a hx, F.strictUpperLayer_le_layer a hy,
    (F.strictUpperLayer a).sub_mem hx ((F.strictUpperLayer a).smul_mem _ hy)⟩

noncomputable def dilationPairLayerEquiv (q : ℚ) (a : σ → ℕ) :
    (F.strictUpperLayer a × F.layer a) ≃ₗ[ℚ] F.dilationPairLayer q a :=
  scaledPairLayerEquiv (F.layer a) (F.strictUpperLayer a).toSubmodule
    (F.strictUpperLayer_le_layer a) (q ^ ∑ i, a i)

end Erdos3.MultidegreeLieFiltration

end

end OAI
