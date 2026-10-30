import DiophantineConsistency.StrictSigmaOneInduction

/-!
# A strict Π₂ normal form for `(∀ x̄, θ) ↔ ¬π`

Let `θ` be a `Σ₀` matrix in `k` variables and `π` a `Σ₁` sentence, and write
`β := bnd π` for the bounded form of `π` (`StrictSigmaOneInduction`), so that
`π ↔ ∃ w, β w` in every model of `𝗜𝚺₁`. The sentence

`normalForm θ π := ∀ w ∀ x̄, ∃ v ∃ ȳ, (¬θ ȳ ∨ ¬β w) ∧ (β v ∨ θ x̄)`

is universally closed over a strict existential prefix with a `Σ₀` matrix
(`matrix_sigma0`), the conclusion shape of the Parsons translation. Here:

* `isigma1_normalForm`: an `𝗜𝚺₁` proof of `(∀ x̄, θ) ↔ ¬π` gives an `𝗜𝚺₁`
  proof of `normalForm θ π` (hence, by `StrictSigmaOneInduction.isigma1_provable`,
  a proof from `𝗣𝗔⁻` and strict `Σ₁` induction).
* `normalForm_valid`: `normalForm θ π → ((∀ x̄, θ) ↔ conB π)` is a theorem of pure
  equality logic, where `conB π := ∀ w, ¬β w` is the strict `Π₁` form of `¬π`.
* `isigma1_conB`: `𝗜𝚺₁ ⊢ ¬π ↔ conB π`.

So a theory proving `normalForm θ π` proves `(∀ x̄, θ) ↔ conB π` by one modus ponens.
-/
set_option autoImplicit false

namespace DiophantineConsistency.StrictPiTwoBridge

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction (bnd StrictSigma eval_bnd_imp eval_bnd_of hierarchy_bnd)

variable {k : ℕ}

/-! ## Index bookkeeping -/

/-- An existential position of the matrix. -/
abbrev eIdx (j : Fin (k + 1)) : Fin ((k + 1) + (k + 1)) := Fin.castAdd (k + 1) j

/-- A universal position of the matrix. -/
abbrev uIdx (j : Fin (k + 1)) : Fin ((k + 1) + (k + 1)) := Fin.natAdd (k + 1) j

theorem appendr_eIdx {M : Type*} (e u : Fin (k + 1) → M) (j : Fin (k + 1)) :
    Matrix.appendr e u (eIdx j) = e j := by
  simp only [Matrix.appendr, Matrix.vecAppend, Function.comp_apply, Fin.cast_eq_self, eIdx,
    Fin.append_left]

theorem appendr_uIdx {M : Type*} (e u : Fin (k + 1) → M) (j : Fin (k + 1)) :
    Matrix.appendr e u (uIdx j) = u j := by
  simp only [Matrix.appendr, Matrix.vecAppend, Function.comp_apply, Fin.cast_eq_self, uIdx,
    Fin.append_right]

theorem fun_fin_one {M : Type*} (w : M) : (fun _ : Fin 1 => w) = ![w] :=
  funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl

theorem snoc_nil {M : Type*} (w : M) : (Fin.snoc (![] : Fin 0 → M) w : Fin 1 → M) = ![w] :=
  funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl

/-! ## The normal form -/

variable (θ : Semisentence ℒₒᵣ k) (π : ArithmeticSentence)

/-- `θ` at the existential variables `ȳ`. -/
def thetaE : Semisentence ℒₒᵣ ((k + 1) + (k + 1)) := θ ⇜ (fun j => #(eIdx j.succ))

/-- `θ` at the universal variables `x̄`. -/
def thetaU : Semisentence ℒₒᵣ ((k + 1) + (k + 1)) := θ ⇜ (fun j => #(uIdx j.succ))

/-- `β` at the existential variable `v`. -/
def betaE : Semisentence ℒₒᵣ ((k + 1) + (k + 1)) := bnd π ⇜ ![#(eIdx (k := k) 0)]

/-- `β` at the universal variable `w`. -/
def betaU : Semisentence ℒₒᵣ ((k + 1) + (k + 1)) := bnd π ⇜ ![#(uIdx (k := k) 0)]

/-- The `Σ₀` matrix of the normal form. -/
def matrix : Semisentence ℒₒᵣ ((k + 1) + (k + 1)) :=
  (∼thetaE θ ⋎ ∼betaU (k := k) π) ⋏ (betaE (k := k) π ⋎ thetaU θ)

/-- **The strict `Π₂` normal form.** -/
def normalForm : ArithmeticSentence := ∀⁰* (∃⁰^[k + 1] matrix θ π)

/-- The strict `Π₁` form of `¬π`. -/
def conB : ArithmeticSentence := ∀⁰ ∼(bnd π)

theorem matrix_sigma0 (hθ : Hierarchy 𝚺 0 θ) (hπ : Hierarchy 𝚺 1 π) :
    Hierarchy 𝚺 0 (matrix θ π) := by
  have hb : Hierarchy 𝚺 0 (bnd π) := hierarchy_bnd hπ le_rfl (fun _ => rfl)
  have hθ' : Hierarchy 𝚷 0 θ := Hierarchy.zero_iff.mp hθ
  have hb' : Hierarchy 𝚷 0 (bnd π) := Hierarchy.zero_iff.mp hb
  simp [matrix, thetaE, thetaU, betaE, betaU, hθ, hθ', hb, hb']

/-! ## Semantics -/

section semantics

variable {M : Type*} [ORingStructure M]

theorem eval_normalForm :
    (normalForm θ π).Evalb (M := M) ![] ↔
      ∀ u : Fin (k + 1) → M, ∃ e : Fin (k + 1) → M,
        (¬θ.Evalb (fun j => e j.succ) ∨ ¬(bnd π).Evalb ![u 0]) ∧
          ((bnd π).Evalb ![e 0] ∨ θ.Evalb (fun j => u j.succ)) := by
  simp only [normalForm, Semiformula.eval_allClosure, Semiformula.eval_exsItr, matrix, thetaE,
    thetaU, betaE, betaU, LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, Semiformula.eval_substs, Semiterm.val_bvar,
    appendr_eIdx, appendr_uIdx, Matrix.cons_val_fin_one, fun_fin_one, Function.comp_def]
  exact Iff.rfl

theorem eval_conB : (conB π).Evalb (M := M) ![] ↔ ∀ w : M, ¬(bnd π).Evalb ![w] := by
  simp [conB]

theorem eval_noZero : (∀⁰* θ).Evalb (M := M) ![] ↔ ∀ x : Fin k → M, θ.Evalb x := by
  simp

/-- **The normal form is the equivalence with the strict consistency form**,
in every structure. -/
theorem eval_normalForm_iff : (normalForm θ π).Evalb (M := M) ![] ↔
    ((∀ x : Fin k → M, θ.Evalb x) ↔ ∀ w : M, ¬(bnd π).Evalb ![w]) := by
  rw [eval_normalForm]
  constructor
  · intro h
    constructor
    · intro hA w hw
      obtain ⟨e, h₁, -⟩ := h (w :> fun _ => 0)
      exact h₁.elim (· (hA _)) (· (by simpa using hw))
    · intro hB x
      obtain ⟨e, -, h₂⟩ := h (0 :> x)
      exact h₂.elim (absurd · (hB _)) (by simpa using ·)
  · intro hE u
    by_cases hb : (bnd π).Evalb ![u 0]
    · obtain ⟨x, hx⟩ := not_forall.mp fun hA => hE.mp hA _ hb
      exact ⟨u 0 :> x, Or.inl (by simpa using hx), Or.inl (by simpa using hb)⟩
    · by_cases hθ : θ.Evalb (fun j => u j.succ)
      · exact ⟨0, Or.inr hb, Or.inr hθ⟩
      · obtain ⟨w, hw⟩ := not_forall_not.mp fun hB => hθ (hE.mpr hB _)
        exact ⟨w :> 0, Or.inr hb, Or.inl (by simpa using hw)⟩

end semantics

/-! ## Provability -/

instance strict_le_isigma1 : 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma ⪯ 𝗜𝚺₁ :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _ <|
    InductionScheme_subset fun {φ} h => by
      obtain ⟨n, D, hD, rfl⟩ := h
      exact Hierarchy.exsItr_iff.mpr (hD.mono (by decide))

section models

variable {M : Type*} [ORingStructure M] [hM : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

include hM in
theorem eval_bnd_iff {π : ArithmeticSentence} (hπ : Hierarchy 𝚺 1 π) :
    π.Evalb (M := M) ![] ↔ ∃ w : M, (bnd π).Evalb ![w] := by
  haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma := models_of_subtheory hM
  constructor
  · intro h
    obtain ⟨w, hw⟩ := eval_bnd_of hπ le_rfl (fun _ => rfl) ![] Empty.elim h
    exact ⟨w, by rwa [snoc_nil] at hw⟩
  · rintro ⟨w, hw⟩
    exact eval_bnd_imp π ![] w Empty.elim (by rwa [snoc_nil])

end models

theorem isigma1_normalForm (hπ : Hierarchy 𝚺 1 π) (h : 𝗜𝚺₁ ⊢ (∀⁰* θ) 🡘 ∼π) :
    𝗜𝚺₁ ⊢ normalForm θ π := by
  refine complete.{0} _ _ fun M _ hM => ?_
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  have hE := models_of_provable hM h
  simp only [models_iff, LogicalConnective.HomClass.map_iff,
    LogicalConnective.HomClass.map_neg] at hE
  rw [models_iff, eval_normalForm_iff, ← eval_noZero, ← not_exists, ← eval_bnd_iff hπ]
  exact ⟨hE.1, hE.2⟩

/-- **Transport back**: `normalForm θ π → ((∀ x̄, θ) ↔ conB π)` in pure equality logic. -/
theorem normalForm_valid : 𝗘𝗤 ℒₒᵣ ⊢ normalForm θ π 🡒 ((∀⁰* θ) 🡘 conB π) := by
  refine complete.{0} _ _ fun M _ _ => ?_
  simp only [models_iff, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_iff]
  intro h
  rw [eval_noZero, eval_conB]
  exact ⟨((eval_normalForm_iff θ π).mp h).mp, ((eval_normalForm_iff θ π).mp h).mpr⟩

/-- **`¬π` and its strict `Π₁` form are `𝗜𝚺₁`-equivalent.** -/
theorem isigma1_conB (hπ : Hierarchy 𝚺 1 π) : 𝗜𝚺₁ ⊢ ∼π 🡘 conB π := by
  refine complete.{0} _ _ fun M _ hM => ?_
  haveI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := hM
  simp only [models_iff, LogicalConnective.HomClass.map_iff, LogicalConnective.HomClass.map_neg]
  rw [eval_conB, eval_bnd_iff hπ]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h ⟨w, hw⟩ => h w hw⟩

end DiophantineConsistency.StrictPiTwoBridge
