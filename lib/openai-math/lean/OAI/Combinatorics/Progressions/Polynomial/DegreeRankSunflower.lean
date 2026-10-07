import OAI.Combinatorics.Progressions.Estimates.LieTreeMultidegree
import OAI.Combinatorics.Progressions.Linear.FurstenbergWeissProjection
import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues

namespace OAI

section

namespace Erdos3

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure DegreeRankLieFiltration (s r : ℕ) where
  rank_le_degree : r ≤ s
  layer : ℕ → ℕ → Submodule ℚ L
  lex_antitone : ∀ {d e i j}, d < e ∨ d = e ∧ i ≤ j → layer e j ≤ layer d i
  one_eq_top : layer 1 0 = ⊤
  rank_zero_eq_one : ∀ d, layer d 0 = layer d 1
  overshoot : ∀ d i, d < i → layer d i = layer (d + 1) 0
  lie_mem : ∀ {d e i j} {x y : L}, x ∈ layer d i → y ∈ layer e j →
    ⁅x, y⁆ ∈ layer (d + e) (i + j)
  terminal : layer s (r + 1) = ⊥

namespace DegreeRankLieFiltration

variable {L} {s r : ℕ} (F : DegreeRankLieFiltration L s r)

theorem degree_antitone (i : ℕ) : Antitone (fun d => F.layer d i) := by
  intro d e hde
  rcases lt_or_eq_of_le hde with h | rfl
  · exact F.lex_antitone (Or.inl h)
  · exact le_rfl

theorem rank_antitone (d : ℕ) : Antitone (F.layer d) := by
  intro i j hij
  exact F.lex_antitone (Or.inr ⟨rfl, hij⟩)

theorem zero_eq_top : F.layer 0 0 = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.degree_antitone 0 (by omega)

theorem layer_eq_bot_of_past_top {d i : ℕ} (h : s < d ∨ s = d ∧ r < i) :
    F.layer d i = ⊥ := by
  apply bot_unique
  apply le_trans (b := F.layer s (r + 1))
  · apply F.lex_antitone
    rcases h with h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩
  · exact F.terminal.le

def associatedDegree : NilpotentLieFiltration L s where
  layer d := F.layer d 0
  antitone := F.degree_antitone 0
  one_eq_top := F.one_eq_top
  lie_mem hx hy := F.lie_mem hx hy
  terminal := F.layer_eq_bot_of_past_top (Or.inl (by omega))

@[simp] theorem associatedDegree_layer (d : ℕ) : F.associatedDegree.layer d = F.layer d 0 := rfl

theorem layer_le_associatedDegree (d i : ℕ) : F.layer d i ≤ F.associatedDegree.layer d :=
  F.rank_antitone d (Nat.zero_le i)

end DegreeRankLieFiltration

namespace NilpotentLieFiltration

variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)

def canonicalDegreeRank : DegreeRankLieFiltration L s s where
  rank_le_degree := le_rfl
  layer := F.rankLayer
  lex_antitone := F.rankLayer_lex_antitone
  one_eq_top := by rw [F.rankLayer_zero, F.one_eq_top]
  rank_zero_eq_one d := by rw [F.rankLayer_zero, F.rankLayer_one]
  overshoot d i h := by rw [F.rankLayer_eq_next_of_degree_lt_rank h, F.rankLayer_zero]
  lie_mem := F.rankLayer_lie_mem
  terminal := F.rankLayer_top_terminal (s + 1) (by omega)

@[simp] theorem canonicalDegreeRank_associatedDegree_layer (d : ℕ) :
    F.canonicalDegreeRank.associatedDegree.layer d = F.layer d := F.rankLayer_zero d

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {ι : Type*} [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ}

def pi (F : ∀ i, DegreeRankLieFiltration (L i) s r) :
    DegreeRankLieFiltration (∀ i, L i) s r where
  rank_le_degree := (F (Classical.choice inferInstance)).rank_le_degree
  layer d j := Submodule.pi Set.univ (fun i => (F i).layer d j)
  lex_antitone h := Submodule.pi_mono (fun i _ => (F i).lex_antitone h)
  one_eq_top := by simp only [one_eq_top, Submodule.pi_top]
  rank_zero_eq_one d := by simp only [rank_zero_eq_one]
  overshoot d j h := congrArg (Submodule.pi Set.univ)
    (funext (fun i => (F i).overshoot d j h))
  lie_mem hx hy i hi := (F i).lie_mem (hx i hi) (hy i hi)
  terminal := by simp only [terminal, Submodule.pi_univ_bot]

@[simp] theorem mem_pi_layer (F : ∀ i, DegreeRankLieFiltration (L i) s r)
    (d j : ℕ) (x : ∀ i, L i) :
    x ∈ (pi F).layer d j ↔ ∀ i, x i ∈ (F i).layer d j := by
  simp [pi, Submodule.mem_pi]

theorem pi_associatedDegree (F : ∀ i, DegreeRankLieFiltration (L i) s r) :
    (pi F).associatedDegree = NilpotentLieFiltration.pi (fun i => (F i).associatedDegree) := rfl

def piLayerEquiv (F : ∀ i, DegreeRankLieFiltration (L i) s r) (d j : ℕ) :
    (∀ i, (F i).layer d j) ≃ₗ[ℚ] (pi F).layer d j where
  toFun x := ⟨fun i => x i, (mem_pi_layer F d j _).mpr (fun i => (x i).property)⟩
  invFun x i := ⟨x.val i, (mem_pi_layer F d j _).mp x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def rankFlag (n : ℕ) : Submodule ℚ L := F.layer (n / (s + 1)) (n % (s + 1))

theorem rankFlag_antitone : Antitone F.rankFlag := by
  intro i j hij
  have hd : i / (s + 1) ≤ j / (s + 1) := Nat.div_le_div_right hij
  rcases lt_or_eq_of_le hd with h | h
  · exact F.lex_antitone (Or.inl h)
  · apply F.lex_antitone (Or.inr ⟨h, ?_⟩)
    have hi := Nat.mod_add_div i (s + 1)
    have hj := Nat.mod_add_div j (s + 1)
    rw [h] at hi
    omega

@[simp] theorem rankFlag_zero : F.rankFlag 0 = ⊤ := by
  simpa only [rankFlag, Nat.zero_div, Nat.zero_mod] using F.zero_eq_top

theorem rankFlag_mul (d : ℕ) : F.rankFlag (d * (s + 1)) = F.layer d 0 := by
  simp [rankFlag, Nat.mul_mod_left]

theorem rankFlag_terminal : F.rankFlag ((s + 1) * (s + 1)) = ⊥ := by
  rw [F.rankFlag_mul]
  exact F.layer_eq_bot_of_past_top (Or.inl (by omega))

theorem rankFlag_lie_mem {n : ℕ} {x y : L} (hy : y ∈ F.rankFlag n) :
    ⁅x, y⁆ ∈ F.rankFlag (n + 1) := by
  have hx : x ∈ F.layer 1 0 := by simp only [F.one_eq_top, Submodule.mem_top]
  have hbr : ⁅x, y⁆ ∈ F.layer (n / (s + 1) + 1) (n % (s + 1)) := by
    simpa only [add_comm 1, zero_add] using F.lie_mem hx hy
  have hzero : ⁅x, y⁆ ∈ F.layer (n / (s + 1) + 1) 0 :=
    F.rank_antitone _ (Nat.zero_le _) hbr
  rw [← F.rankFlag_mul] at hzero
  apply F.rankFlag_antitone _ hzero
  have hmod : n % (s + 1) < s + 1 := Nat.mod_lt n (by omega)
  have heq := Nat.mod_add_div n (s + 1)
  rw [add_mul, one_mul, Nat.mul_comm (n / (s + 1)) (s + 1)]
  omega

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (F : NilpotentLieFiltration L s) (G : DegreeRankLieFiltration M t r)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ d, ∀ x ∈ F.layer d, φ x ∈ G.layer d 0)

include hφ in
theorem FilteredLieTree.map_eval_mem_degreeRank {d k : ℕ} (a : FilteredLieTree F d k) :
    φ a.eval ∈ G.layer d k := by
  induction a with
  | leaf hd x hx =>
    rw [FilteredLieTree.eval_leaf, ← G.rank_zero_eq_one]
    exact hφ _ x hx
  | bracket a b ha hb =>
    rw [FilteredLieTree.eval_bracket, φ.map_lie]
    exact G.lie_mem ha hb

include hφ in
theorem NilpotentLieFiltration.map_rankLayer {d k : ℕ} {x : L}
    (hx : x ∈ F.rankLayer d k) : φ x ∈ G.layer d k := by
  have hle : F.rankLayer d k ≤ (G.layer d k).comap φ.toLinearMap := by
    apply sup_le
    · intro y hy
      exact G.lex_antitone (Or.inl (Nat.lt_succ_self d)) (hφ (d + 1) y hy)
    · apply Submodule.span_le.mpr
      rintro y ⟨n, hn, a, rfl⟩
      exact G.rank_antitone d hn (a.map_eval_mem_degreeRank F G φ hφ)
  exact hle hx

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def rankSubgroup (d r : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.rankIdeal d r).toLieSubalgebra

@[simp] theorem mem_rankSubgroup (d r : ℕ) (x : F.Group) :
    x ∈ F.rankSubgroup d r ↔ x.coord ∈ F.rankLayer d r := Iff.rfl

theorem rankSubgroup_normal (d r : ℕ) : (F.rankSubgroup d r).Normal :=
  NilpotentLieBCHGroup.subgroup_ideal_normal (F.rankIdeal d r)

theorem rankSubgroup_le_subgroup (d r : ℕ) : F.rankSubgroup d r ≤ F.subgroup d :=
  fun _ hx => F.rankLayer_le_layer d r hx

theorem rankSubgroup_zero (d : ℕ) : F.rankSubgroup d 0 = F.subgroup d := by
  ext x
  change x.coord ∈ F.rankLayer d 0 ↔ x.coord ∈ F.layer d
  rw [F.rankLayer_zero]

theorem rankSubgroup_one (d : ℕ) : F.rankSubgroup d 1 = F.subgroup d := by
  ext x
  change x.coord ∈ F.rankLayer d 1 ↔ x.coord ∈ F.layer d
  rw [F.rankLayer_one]

theorem rankSubgroup_lex_antitone {d e r t : ℕ} (h : d < e ∨ d = e ∧ r ≤ t) :
    F.rankSubgroup e t ≤ F.rankSubgroup d r := fun _ hx => F.rankLayer_lex_antitone h hx

theorem rankSubgroup_overshoot {d r : ℕ} (h : d < r) :
    F.rankSubgroup d r = F.subgroup (d + 1) := by
  ext x
  change x.coord ∈ F.rankLayer d r ↔ x.coord ∈ F.layer (d + 1)
  rw [F.rankLayer_eq_next_of_degree_lt_rank h]

theorem rankSubgroup_commutator_mem {d e r t : ℕ} {x y : F.Group}
    (hx : x ∈ F.rankSubgroup d r) (hy : y ∈ F.rankSubgroup e t) :
    x * y * x⁻¹ * y⁻¹ ∈ F.rankSubgroup (d + e) (r + t) :=
  NilpotentLieBCHGroup.commutator_mem_ideal (F.rankIdeal (d + e) (r + t)) x y
    (F.rankLayer_lie_mem hx hy)

theorem rankSubgroup_eq_bot_of_degree_gt {d : ℕ} (hd : s < d) (r : ℕ) :
    F.rankSubgroup d r = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply NilpotentLieBCHGroup.ext
  change x.coord = 0
  have h := (F.mem_rankSubgroup d r x).mp hx
  simpa only [F.rankLayer_eq_bot_of_degree_gt hd r, Submodule.mem_bot] using h

theorem rankSubgroup_top_terminal : F.rankSubgroup s (s + 1) = ⊥ := by
  rw [F.rankSubgroup_overshoot (by omega), F.subgroup_terminal]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def polynomialFiltration : DegreeRankLieFiltration (VectorPolynomial σ ℚ L) s r where
  rank_le_degree := F.rank_le_degree
  layer d i := coefficientSubmodule (F.layer d i)
  lex_antitone := fun h _ hp α => F.lex_antitone h (hp α)
  one_eq_top := by
    apply top_unique
    intro p _ α
    rw [F.one_eq_top]
    trivial
  rank_zero_eq_one d := by rw [F.rank_zero_eq_one]
  overshoot d i hi := by rw [F.overshoot d i hi]
  lie_mem := by
    intro d e i j p q hp hq
    apply (eval_mem_iff_coefficients (F.layer (d + e) (i + j)) ⁅p, q⁆).mp
    intro t
    have hp' := (eval_mem_iff_coefficients (F.layer d i) p).mpr hp t
    have hq' := (eval_mem_iff_coefficients (F.layer e j) q).mpr hq t
    change evalLie t ⁅p, q⁆ ∈ F.layer (d + e) (i + j)
    rw [LieHom.map_lie]
    exact F.lie_mem hp' hq'
  terminal := by
    apply bot_unique
    intro p hp
    change p = 0
    apply coefficients.injective
    ext α
    simpa only [F.terminal, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using hp α

@[simp] theorem polynomialFiltration_layer (d i : ℕ) :
    (F.polynomialFiltration (σ := σ)).layer d i = coefficientSubmodule (F.layer d i) := rfl

theorem monomial_mem_polynomialFiltration (d i : ℕ) (α : σ →₀ ℕ) {x : L}
    (hx : x ∈ F.layer d i) :
    monomial (R := ℚ) α x ∈ (F.polynomialFiltration (σ := σ)).layer d i :=
  monomial_mem_coefficientSubmodule (F.layer d i) α hx

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem lieTreeEval_mem (v : I → L) (d k : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) (k i)) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.layer (lieTreeWeight d a) (lieTreeWeight k a) := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.lie_mem ha hb

theorem lieTreeEval_mem_length (v : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (a : FreeMagma I) :
    lieTreeEval v a ∈ F.layer (lieTreeWeight d a) a.length := by
  induction a using FreeMagma.rec with
  | of i => exact hv i
  | mul a b ha hb => exact F.lie_mem ha hb

theorem lieTreeEval_sub_mem (v w : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (hw : ∀ i, w i ∈ F.layer (d i) 1)
    (hvw : ∀ i, v i - w i ∈ F.layer (d i) 2) (a : FreeMagma I) :
    lieTreeEval v a - lieTreeEval w a ∈
      F.layer (lieTreeWeight d a) (a.length + 1) := by
  induction a using FreeMagma.rec with
  | of i => exact hvw i
  | mul a b ha hb =>
    have h₁ := F.lie_mem ha (F.lieTreeEval_mem_length v d hv b)
    have h₂ := F.lie_mem (F.lieTreeEval_mem_length w d hw a) hb
    have heq : lieTreeEval v (a.mul b) - lieTreeEval w (a.mul b) =
        ⁅lieTreeEval v a - lieTreeEval w a, lieTreeEval v b⁆ +
          ⁅lieTreeEval w a, lieTreeEval v b - lieTreeEval w b⁆ := by
      simp only [lieTreeEval, sub_lie, lie_sub]
      abel
    rw [heq]
    apply Submodule.add_mem
    · simpa only [lieTreeWeight, FreeMagma.length, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h₁
    · simpa only [lieTreeWeight, FreeMagma.length, Nat.add_assoc] using h₂

theorem top_lieTreeEval_congr (v w : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (hw : ∀ i, w i ∈ F.layer (d i) 1)
    (hvw : ∀ i, v i - w i ∈ F.layer (d i) 2) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r) :
    lieTreeEval v a = lieTreeEval w a := by
  have h := F.lieTreeEval_sub_mem v w d hv hw hvw a
  rw [hd, hr, F.terminal, Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem rankFlag_encode (i j : ℕ) (hj : j ≤ s) :
    F.rankFlag (i * (s + 1) + j) = F.layer i j := by
  have hA : 0 < s + 1 := by omega
  have hjA : j < s + 1 := by omega
  unfold rankFlag
  rw [Nat.mul_comm i (s + 1), Nat.mul_add_div hA, Nat.div_eq_of_lt hjA,
    add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hjA]

theorem rankFlag_encode_lt (i j : ℕ) (hi : i ≤ s) (hj : j ≤ s) :
    i * (s + 1) + j < (s + 1) * (s + 1) := by
  have h := Nat.mul_le_mul_right (s + 1) hi
  nlinarith

theorem rankFlag_decode_lt {k : ℕ} (hk : k < (s + 1) * (s + 1)) :
    k / (s + 1) ≤ s ∧ k % (s + 1) ≤ s := by
  have hA : 0 < s + 1 := by omega
  have hdiv := (Nat.div_lt_iff_lt_mul hA).mpr hk
  have hmod : k % (s + 1) < s + 1 := Nat.mod_lt k hA
  omega

theorem layer_eq_rankFlag (i j : ℕ) :
    ∃ k : Fin ((s + 1) * (s + 1) + 1), F.layer i j = F.rankFlag k.val := by
  by_cases hi : i ≤ s
  · by_cases hj : j ≤ s
    · exact ⟨⟨i * (s + 1) + j, by have := rankFlag_encode_lt i j hi hj; omega⟩,
        (F.rankFlag_encode i j hj).symm⟩
    · rw [F.overshoot i j (by omega)]
      refine ⟨⟨(i + 1) * (s + 1), ?_⟩, (F.rankFlag_mul (i + 1)).symm⟩
      have h := Nat.mul_le_mul_right (s + 1) (show i + 1 ≤ s + 1 by omega)
      omega
  · refine ⟨⟨(s + 1) * (s + 1), by omega⟩, ?_⟩
    rw [F.rankFlag_terminal, F.layer_eq_bot_of_past_top (Or.inl (by omega))]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def higherHorizontalKernel (i : ℕ) : Submodule ℚ (F.layer i 1) :=
  (F.layer i 2).comap (F.layer i 1).subtype

abbrev HigherHorizontal (i : ℕ) := (F.layer i 1) ⧸ F.higherHorizontalKernel i

def higherHorizontalMk (i : ℕ) : F.layer i 1 →ₗ[ℚ] F.HigherHorizontal i :=
  (F.higherHorizontalKernel i).mkQ

theorem higherHorizontalMk_eq (i : ℕ) (x y : F.layer i 1) :
    F.higherHorizontalMk i x = F.higherHorizontalMk i y ↔ x.val - y.val ∈ F.layer i 2 :=
  Submodule.Quotient.eq (F.higherHorizontalKernel i)

theorem higherHorizontalMk_surjective (i : ℕ) : Function.Surjective (F.higherHorizontalMk i) :=
  (F.higherHorizontalKernel i).mkQ_surjective

noncomputable def higherHorizontalRepresentative (i : ℕ) (v : F.HigherHorizontal i) : F.layer i 1 := by
  classical
  exact if v = 0 then 0 else Classical.choose (F.higherHorizontalMk_surjective i v)

@[simp] theorem higherHorizontalRepresentative_zero (i : ℕ) :
    F.higherHorizontalRepresentative i 0 = 0 := by
  classical
  simp [higherHorizontalRepresentative]

theorem higherHorizontalMk_representative (i : ℕ) (v : F.HigherHorizontal i) :
    F.higherHorizontalMk i (F.higherHorizontalRepresentative i v) = v := by
  classical
  by_cases hv : v = 0
  · simp [higherHorizontalRepresentative, hv]
  · simpa [higherHorizontalRepresentative, hv] using
      Classical.choose_spec (F.higherHorizontalMk_surjective i v)

noncomputable def horizontalTreeValue (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, F.HigherHorizontal (d i)) : L :=
  lieTreeEval (fun i => (F.higherHorizontalRepresentative (d i) (v i)).val) a

theorem horizontalTreeValue_mem (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, F.HigherHorizontal (d i)) :
    F.horizontalTreeValue d a v ∈ F.layer (lieTreeWeight d a) a.length :=
  F.lieTreeEval_mem_length _ d (fun i => (F.higherHorizontalRepresentative (d i) (v i)).property) a

theorem horizontalTreeValue_mk (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r) (v : ∀ i, F.layer (d i) 1) :
    F.horizontalTreeValue d a (fun i => F.higherHorizontalMk (d i) (v i)) =
      lieTreeEval (fun i => (v i).val) a := by
  apply F.top_lieTreeEval_congr _ _ d
    (fun i => (F.higherHorizontalRepresentative (d i) (F.higherHorizontalMk (d i) (v i))).property)
    (fun i => (v i).property) _ a hd hr
  intro i
  exact (F.higherHorizontalMk_eq (d i) _ _).mp (F.higherHorizontalMk_representative _ _)

theorem horizontalTreeValue_zero_of_leaf (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, F.HigherHorizontal (d i)) {i : I} (hi : i ∈ lieTreeSupport a)
    (hv : v i = 0) : F.horizontalTreeValue d a v = 0 := by
  apply lieTreeEval_eq_zero_of_leaf _ a hi
  simp only [hv, higherHorizontalRepresentative_zero, ZeroMemClass.coe_zero]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def fourHorizontalLayer (d : ℕ) : Submodule ℚ (Fin 4 → L) :=
  Submodule.pi Set.univ (fun _ => F.layer d 1)

theorem mem_fourHorizontalLayer (d : ℕ) (v : Fin 4 → L) :
    v ∈ F.fourHorizontalLayer d ↔ ∀ k, v k ∈ F.layer d 1 := by
  simp [fourHorizontalLayer, Submodule.mem_pi]

def fourHorizontalMap (d : ℕ) : F.fourHorizontalLayer d →ₗ[ℚ] (Fin 4 → F.HigherHorizontal d) where
  toFun v k := F.higherHorizontalMk d ⟨v.val k, (F.mem_fourHorizontalLayer d v.val).mp v.property k⟩
  map_add' x y := by
    funext k
    exact map_add (F.higherHorizontalMk d)
      ⟨x.val k, (F.mem_fourHorizontalLayer d x.val).mp x.property k⟩
      ⟨y.val k, (F.mem_fourHorizontalLayer d y.val).mp y.property k⟩
  map_smul' c x := by
    funext k
    exact map_smul (F.higherHorizontalMk d) c
      ⟨x.val k, (F.mem_fourHorizontalLayer d x.val).mp x.property k⟩

def fourHorizontalImage (K : LieSubalgebra ℚ (Fin 4 → L)) (d : ℕ) :
    Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  (K.toSubmodule.comap (F.fourHorizontalLayer d).subtype).map (F.fourHorizontalMap d)

theorem mem_fourHorizontalImage (K : LieSubalgebra ℚ (Fin 4 → L)) (d : ℕ)
    (v : Fin 4 → F.HigherHorizontal d) :
    v ∈ F.fourHorizontalImage K d ↔
      ∃ w : F.fourHorizontalLayer d, w.val ∈ K ∧ F.fourHorizontalMap d w = v := Iff.rfl

theorem fourHorizontalImage_frequency {E : Type*} [AddCommGroup E] [Module ℚ E]
    (K : LieSubalgebra ℚ (Fin 4 → L)) (η : L →ₗ[ℚ] E)
    (hK : ∀ x ∈ K, (∀ k, x k ∈ F.layer s r) →
      η (x 0) + η (x 1) - η (x 2) - η (x 3) = 0)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : ∀ i, Fin 4 → F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ F.fourHorizontalImage K (d i)) :
    η (F.horizontalTreeValue d a (fun i => v i 0)) +
      η (F.horizontalTreeValue d a (fun i => v i 1)) -
      η (F.horizontalTreeValue d a (fun i => v i 2)) -
      η (F.horizontalTreeValue d a (fun i => v i 3)) = 0 := by
  classical
  have hlift (i : I) := (F.mem_fourHorizontalImage K (d i) (v i)).mp (hv i)
  choose w hwK hwm using hlift
  let u (i : I) : Fin 4 → L := (w i).val
  let lifted (k : Fin 4) (i : I) : F.layer (d i) 1 :=
    ⟨u i k, (F.mem_fourHorizontalLayer (d i) (w i).val).mp (w i).property k⟩
  have hmap (k : Fin 4) :
      (fun i => F.higherHorizontalMk (d i) (lifted k i)) = (fun i => v i k) := by
    funext i
    exact congrFun (hwm i) k
  have hvalue (k : Fin 4) : F.horizontalTreeValue d a (fun i => v i k) = lieTreeEval u a k := by
    rw [← hmap k]
    exact (F.horizontalTreeValue_mk d a hd hr (lifted k)).trans (lieTreeEval_pi u a k).symm
  have htree : lieTreeEval u a ∈ K := by
    have hmem (t : FreeMagma I) : lieTreeEval u t ∈ K := by
      induction t using FreeMagma.rec with
      | of i => exact hwK i
      | mul a b ha hb => exact K.lie_mem ha hb
    exact hmem a
  have htop (k : Fin 4) : lieTreeEval u a k ∈ F.layer s r := by
    rw [lieTreeEval_pi]
    simpa only [hd, hr] using F.lieTreeEval_mem_length (fun i => u i k) d
      (fun i => (lifted k i).property) a
  rw [hvalue 0, hvalue 1, hvalue 2, hvalue 3]
  exact hK _ htree htop

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L E : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup E] [Module ℚ E]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r)

theorem sunflower_horizontal_bracket
    (K : LieSubalgebra ℚ (Fin 4 → L)) (η : L →ₗ[ℚ] E)
    (hK : ∀ x ∈ K, (∀ k, x k ∈ F.layer s r) →
      η (x 0) + η (x 1) - η (x 2) - η (x 3) = 0)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : ∀ i, F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ fourFirstProjection (F.fourHorizontalImage K (d i)))
    (i j : I) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ fourDependentProjection (F.fourHorizontalImage K (d i)))
    (hvj : v j ∈ fourDependentProjection (F.fourHorizontalImage K (d j))) :
    η (F.horizontalTreeValue d a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a) (F.horizontalTreeValue d a)
    (fun u k hk hu => F.horizontalTreeValue_zero_of_leaf d a u (i := k) hk hu)
    η (map_zero η) (fun k => F.fourHorizontalImage K (d k))
    (F.fourHorizontalImage_frequency K η hK d a hd hr) v hv i j hij hi hj hvi hvj

theorem sunflower_representative_bracket
    (K : LieSubalgebra ℚ (Fin 4 → L)) (η : L →ₗ[ℚ] E)
    (hK : ∀ x ∈ K, (∀ k, x k ∈ F.layer s r) →
      η (x 0) + η (x 1) - η (x 2) - η (x 3) = 0)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : ∀ i, F.layer (d i) 1)
    (hv : ∀ i, F.higherHorizontalMk (d i) (v i) ∈
      fourFirstProjection (F.fourHorizontalImage K (d i)))
    (i j : I) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : F.higherHorizontalMk (d i) (v i) ∈
      fourDependentProjection (F.fourHorizontalImage K (d i)))
    (hvj : F.higherHorizontalMk (d j) (v j) ∈
      fourDependentProjection (F.fourHorizontalImage K (d j))) :
    η (lieTreeEval (fun i => (v i).val) a) = 0 := by
  have h := F.sunflower_horizontal_bracket K η hK d a hd hr
    (fun k => F.higherHorizontalMk (d k) (v k)) hv i j hij hi hj hvi hvj
  rwa [F.horizontalTreeValue_mk d a hd hr v] at h

end Erdos3.DegreeRankLieFiltration

end

end OAI
