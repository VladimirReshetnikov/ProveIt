import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Estimates.BlockSubsetCount
import OAI.Combinatorics.Progressions.Nilpotent.SquarefreeBracketCoefficients
import OAI.Combinatorics.Progressions.Polynomial.SquarefreeBlockDegree

namespace OAI

section

namespace Erdos3

variable {ι σ : Type*} [Fintype ι]

noncomputable def SquarefreeIndex.ofFinset (S : Finset ι) : SquarefreeIndex ι := by
  classical
  exact ⟨Finsupp.equivFunOnFinite.symm (fun i => if i ∈ S then 1 else 0),
    fun i => by
      change (if i ∈ S then 1 else 0) ≤ 1
      split_ifs <;> omega⟩

theorem SquarefreeIndex.ofFinset_apply [DecidableEq ι] (S : Finset ι) (i : ι) :
    (ofFinset S).val i = if i ∈ S then 1 else 0 := by
  classical
  simp [ofFinset]

theorem SquarefreeIndex.support_ofFinset (S : Finset ι) : (ofFinset S).val.support = S := by
  classical
  ext i
  simp only [Finsupp.mem_support_iff, ofFinset_apply]
  split_ifs <;> simp_all

theorem SquarefreeIndex.ofFinset_support (a : SquarefreeIndex ι) : ofFinset a.val.support = a := by
  classical
  apply Subtype.ext
  ext i
  rw [ofFinset_apply]
  have hi := a.property i
  split_ifs with h
  · have := Finsupp.mem_support_iff.mp h
    omega
  · exact (Finsupp.notMem_support_iff.mp h).symm

theorem SquarefreeIndex.ofFinset_add_complement [DecidableEq ι] (S T : Finset ι) (hST : S ⊆ T) :
    (ofFinset S).val + (ofFinset (T \ S)).val = (ofFinset T).val := by
  classical
  ext i
  simp only [Finsupp.add_apply, ofFinset_apply, Finset.mem_sdiff]
  by_cases hi : i ∈ S
  · simp only [hi, hST hi, not_true_eq_false, and_false, ite_true, ite_false, add_zero]
  · by_cases hj : i ∈ T <;> simp [hi, hj]

theorem SquarefreeIndex.blockDegree_ofFinset [DecidableEq σ] (π : ι → σ)
    (S : Finset ι) (i : σ) :
    blockDegree π (ofFinset S).val i = (S.filter fun j => π j = i).card := by
  classical
  rw [blockDegree_apply]
  simp only [ofFinset_apply]
  have h : (fun j => if π j = i then (if j ∈ S then 1 else 0) else 0) =
      (fun j => if j ∈ S ∧ π j = i then 1 else 0) := by
    funext j
    split_ifs <;> simp_all
  rw [h]
  have hs : (Finset.univ.filter fun j => j ∈ S ∧ π j = i) =
      S.filter (fun j => π j = i) := by ext j; simp
  simpa only [Finset.sum_boole, Nat.cast_id] using congrArg Finset.card hs

theorem SquarefreeIndex.blockDegree_support [DecidableEq σ] (π : ι → σ)
    (a : SquarefreeIndex ι) (i : σ) :
    blockDegree π a.val i = (a.val.support.filter fun j => π j = i).card := by
  rw [← blockDegree_ofFinset π a.val.support i, ofFinset_support]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def fullShiftExponent (n : ℕ) : Fin n →₀ ℕ :=
  (SquarefreeIndex.ofFinset (Finset.univ : Finset (Fin n))).val

theorem fullShiftExponent_apply (n : ℕ) (i : Fin n) : fullShiftExponent n i = 1 := by
  simp only [fullShiftExponent, SquarefreeIndex.ofFinset_apply, Finset.mem_univ, ite_true]

theorem fullShiftExponent_sum (n : ℕ) : (fullShiftExponent n).sum (fun _ e => e) = n := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [fullShiftExponent_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]

theorem exponent_eq_full_or_missing {n : ℕ} (d : Fin n →₀ ℕ)
    (hd : d.sum (fun _ e => e) ≤ n) : d = fullShiftExponent n ∨ ∃ i, d i = 0 := by
  by_cases hz : ∃ i, d i = 0
  · exact Or.inr hz
  left
  have hpos (i : Fin n) : 1 ≤ d i := by
    have hn : d i ≠ 0 := fun hi => hz ⟨i, hi⟩
    omega
  have hsum : (∑ i, d i) ≤ n := by
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hd
  ext i
  rw [fullShiftExponent_apply]
  by_contra hi
  have hstrict : (1 : ℕ) < d i := by have := hpos i; omega
  have hlt := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hpos j)
    ⟨i, Finset.mem_univ i, hstrict⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hlt
  omega

end Erdos3

end

section

namespace Erdos3

variable {ι σ : Type*} [Fintype ι]

omit [Fintype ι] in
theorem SquarefreeIndex.support_subset_of_add (a b c : SquarefreeIndex ι)
    (h : a.val + b.val = c.val) : a.val.support ⊆ c.val.support := by
  intro i hi
  apply Finsupp.mem_support_iff.mpr
  have ha := Finsupp.mem_support_iff.mp hi
  have hs := congrArg (fun u : ι →₀ ℕ => u i) h
  simp only [Finsupp.add_apply] at hs
  omega

abbrev SquarefreeSplit (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ) :=
  {p : SquarefreeIndex ι × SquarefreeIndex ι //
    p.1.val + p.2.val = c.val ∧ blockDegree π p.1.val = a ∧ blockDegree π p.2.val = b}

theorem squarefreeSplit_ext (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (p q : SquarefreeSplit π c a b) (h : p.val.1 = q.val.1) : p = q := by
  apply Subtype.ext
  apply Prod.ext h
  apply Subtype.ext
  have hs := p.property.1.trans q.property.1.symm
  rw [h] at hs
  exact add_left_cancel hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι κ σ : Type*}

def SquarefreeIndex.permute (e : ι ≃ κ) : SquarefreeIndex ι ≃ SquarefreeIndex κ where
  toFun a := ⟨Finsupp.equivMapDomain e a.val, fun j => a.property (e.symm j)⟩
  invFun b := ⟨Finsupp.equivMapDomain e.symm b.val, fun i => b.property (e i)⟩
  left_inv a := Subtype.ext ((Finsupp.equivCongrLeft e).left_inv a.val)
  right_inv b := Subtype.ext ((Finsupp.equivCongrLeft e).right_inv b.val)

@[simp] theorem SquarefreeIndex.permute_apply (e : ι ≃ κ) (a : SquarefreeIndex ι) (j : κ) :
    (permute e a).val j = a.val (e.symm j) := rfl

theorem SquarefreeIndex.permute_symm (e : ι ≃ κ) : (permute e).symm = permute e.symm := rfl

theorem SquarefreeIndex.permute_disjoint (e : ι ≃ κ) (a b : SquarefreeIndex ι) :
    Disjoint (permute e a).val.support (permute e b).val.support ↔
      Disjoint a.val.support b.val.support := Finset.disjoint_map e.toEmbedding

theorem SquarefreeIndex.permute_disjointAdd (e : ι ≃ κ) (a b : SquarefreeIndex ι)
    (hab : Disjoint a.val.support b.val.support) :
    permute e (a.disjointAdd b hab) =
      (permute e a).disjointAdd (permute e b) ((permute_disjoint e a b).mpr hab) := by
  apply Subtype.ext
  ext j
  rfl

theorem SquarefreeIndex.permute_zero_iff (e : ι ≃ κ) (a : SquarefreeIndex ι) :
    (permute e a).val = 0 ↔ a.val = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun c : κ →₀ ℕ => c (e i)) h
    simpa only [permute_apply, Equiv.symm_apply_apply, Finsupp.zero_apply] using hi
  · intro h
    ext j
    simp only [permute_apply, h, Finsupp.zero_apply]

theorem SquarefreeIndex.permute_total [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : SquarefreeIndex ι) :
    (∑ j, (permute e a).val j) = ∑ i, a.val i :=
  Equiv.sum_comp e.symm (fun i => a.val i)

theorem SquarefreeIndex.permute_blockDegree [Fintype ι] (π : ι → σ)
    (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    blockDegree π (permute e a).val = blockDegree π a.val := by
  classical
  ext i
  simp only [blockDegree_apply, permute_apply]
  calc
    (∑ j, if π j = i then a.val (e.symm j) else 0) =
        ∑ j, if π (e j) = i then a.val j else 0 := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp e (fun j => if π j = i then a.val (e.symm j) else 0)).symm
    _ = _ := by simp only [he]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ]

noncomputable def blockExponent (π : ι → σ) (a : ι →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (blockDegree π a)

@[simp] theorem blockExponent_apply (π : ι → σ) (a : ι →₀ ℕ) (i : σ) :
    blockExponent π a i = blockDegree π a i := rfl

@[simp] theorem blockExponent_zero (π : ι → σ) : blockExponent π 0 = 0 := by
  ext i
  simp only [blockExponent_apply, blockDegree_zero, Pi.zero_apply, Finsupp.zero_apply]

theorem blockExponent_permute (π : ι → σ) (e : Equiv.Perm ι)
    (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    blockExponent π (SquarefreeIndex.permute e a).val = blockExponent π a.val := by
  ext i
  simp only [blockExponent_apply, SquarefreeIndex.permute_blockDegree π e he a]

def multidegreeFactorial (a : σ → ℕ) : ℕ := ∏ i, (a i).factorial

theorem multidegreeFactorial_pos (a : σ → ℕ) : 0 < multidegreeFactorial a :=
  Finset.prod_pos fun i _ => Nat.factorial_pos (a i)

end Erdos3

end

section

namespace Erdos3

theorem SquarefreeIndex.permute_weight {ι κ : Type*} (e : ι ≃ κ)
    (a : SquarefreeIndex ι) (x : ι → ℚ) :
    ((permute e a).val.prod fun j n => x (e.symm j) ^ n) =
      a.val.prod (fun i n => x i ^ n) := by
  change (Finsupp.equivMapDomain e a.val).prod _ = _
  rw [Finsupp.prod_equivMapDomain]
  simp only [Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [Fintype σ]

def blockSplitMultiplicity (a b : σ → ℕ) : ℕ := ∏ i, (a i + b i).choose (a i)

theorem multidegreeFactorial_split (a b : σ → ℕ) :
    multidegreeFactorial a * multidegreeFactorial b * blockSplitMultiplicity a b =
      multidegreeFactorial (a + b) := by
  simp only [multidegreeFactorial, blockSplitMultiplicity, ← Finset.prod_mul_distrib, Pi.add_apply]
  apply Finset.prod_congr rfl
  intro i _
  have h := Nat.add_choose_mul_factorial_mul_factorial (b i) (a i)
  rw [Nat.add_comm (b i) (a i)] at h
  calc
    (a i).factorial * (b i).factorial * (a i + b i).choose (a i) =
        (a i + b i).choose (a i) * (b i).factorial * (a i).factorial := by ac_rfl
    _ = _ := h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι] [DecidableEq σ]

noncomputable def squarefreeSplitSubsetEquiv (π : ι → σ) (c : SquarefreeIndex ι)
    (a b : σ → ℕ) (hc : blockDegree π c.val = a + b) :
    SquarefreeSplit π c a b ≃
      {T : Finset ι // T ⊆ c.val.support ∧ ∀ i, (T.filter fun j => π j = i).card = a i} where
  toFun p := ⟨p.val.1.val.support, by
    refine ⟨SquarefreeIndex.support_subset_of_add _ _ _ p.property.1, ?_⟩
    intro i
    rw [← SquarefreeIndex.blockDegree_support π p.val.1 i, p.property.2.1]⟩
  invFun T := by
    let u := SquarefreeIndex.ofFinset T.val
    let v := SquarefreeIndex.ofFinset (c.val.support \ T.val)
    have huv : u.val + v.val = c.val := by
      have h := SquarefreeIndex.ofFinset_add_complement T.val c.val.support T.property.1
      simpa only [SquarefreeIndex.ofFinset_support] using h
    have hu : blockDegree π u.val = a := by
      ext i
      exact (SquarefreeIndex.blockDegree_ofFinset π T.val i).trans (T.property.2 i)
    have hv : blockDegree π v.val = b := by
      have h := congrArg (blockDegree π) huv
      rw [blockDegree_add, hu, hc] at h
      exact add_left_cancel h
    exact ⟨(u, v), huv, hu, hv⟩
  left_inv p := squarefreeSplit_ext π c a b _ _ (SquarefreeIndex.ofFinset_support p.val.1)
  right_inv T := Subtype.ext (SquarefreeIndex.support_ofFinset T.val)

theorem card_squarefreeSplit (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (hc : blockDegree π c.val = a + b) :
    Fintype.card (SquarefreeSplit π c a b) = blockSplitMultiplicity a b := by
  classical
  rw [Fintype.card_congr (squarefreeSplitSubsetEquiv π c a b hc), card_blockSubsets]
  unfold blockSplitMultiplicity
  apply Finset.prod_congr rfl
  intro i _
  rw [← SquarefreeIndex.blockDegree_support π c i, hc, Pi.add_apply]

omit [Fintype σ] [DecidableEq ι] [DecidableEq σ] in
theorem squarefreeSplit_degree (π : ι → σ) (c : SquarefreeIndex ι) (a b : σ → ℕ)
    (p : SquarefreeSplit π c a b) : blockDegree π c.val = a + b := by
  rw [← p.property.1, blockDegree_add, p.property.2.1, p.property.2.2]

end Erdos3

end

end OAI
