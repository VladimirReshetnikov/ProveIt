import Foundation.FirstOrder.Arithmetic.Schemata

/-!
# Strict Σ₁ induction proves Foundation's `𝗜𝚺₁`

Foundation's class `Hierarchy 𝚺 1` admits bounded universal quantifiers over
unbounded existentials, so an `𝗜𝚺₁` proof may use induction on predicates that
are not of the strict form `∃⁰^[n] D` with a bounded (`Σ₀`) matrix `D`. This
module proves that strict induction suffices:

`theory_le : 𝗜𝚺₁ ⪯ 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma`.

The proof is semantic. In a model of `𝗣𝗔⁻` plus strict induction:

* `bnd φ` bounds every unbounded existential of `φ` by one new last bound
  variable `w`. It always implies `φ` (`eval_bnd_imp`) and is monotone in `w`
  (`eval_bnd_mono`); for `Σ₁` formulas it is `Σ₀` (`hierarchy_bnd`).
* Strict induction proves collection for monotone `Σ₀` bodies (`collection`).
* Hence every `Σ₁` formula is equivalent to the strict `∃ w, bnd φ`
  (`eval_bnd_of`), and its induction axiom follows from a strict one.

Completeness turns the model statement into `theory_le`. `StrictSigma` is
definitionally `ParsonsStrictInvariant.Strict`.
-/
set_option autoImplicit false

namespace DiophantineConsistency.StrictSigmaOneInduction

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-- Syntactically strict existential prefix with a bounded matrix. -/
def StrictSigma (φ : ArithmeticSemiformula ℕ 1) : Prop :=
  ∃ (n : ℕ) (D : ArithmeticSemiformula ℕ (1 + n)), Hierarchy 𝚺 0 D ∧ φ = ∃⁰^[n] D

variable {ξ : Type*}

/-! ## Bounding the existentials -/

/-- The bound variable of `bnd`, in the scope of one further binder. -/
abbrev lastVar (n : ℕ) : ArithmeticSemiterm ξ (n + 2) := #(Fin.last (n + 1))

/-- **Every unbounded existential bounded by a new last bound variable.** -/
def bnd : {n : ℕ} → ArithmeticSemiformula ξ n → ArithmeticSemiformula ξ (n + 1)
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | n, .rel r v => Rew.castLE (Nat.le_succ n) ▹ Semiformula.rel r v
  | n, .nrel r v => Rew.castLE (Nat.le_succ n) ▹ Semiformula.nrel r v
  | _, φ ⋏ ψ => bnd φ ⋏ bnd ψ
  | _, φ ⋎ ψ => bnd φ ⋎ bnd ψ
  | _, ∀⁰ φ => ∀⁰ bnd φ
  | n, ∃⁰ φ => ∃⁰[“x. x < !!(lastVar (ξ := ξ) n)”] bnd φ

/-! ## `bnd φ` is bounded -/

@[simp] theorem lastVar_positive (n : ℕ) : (lastVar (ξ := ξ) n).Positive := by
  simp [lastVar, Fin.lt_def]

/-- On open formulas `bnd` is the plain embedding. -/
theorem bnd_open : ∀ {n : ℕ} (φ : ArithmeticSemiformula ξ n), φ.Open →
    bnd φ = Rew.castLE (Nat.le_succ n) ▹ φ
  | _, ⊤, _ => by simp [bnd]
  | _, ⊥, _ => by simp [bnd]
  | _, .rel _ _, _ => rfl
  | _, .nrel _ _, _ => rfl
  | _, φ ⋏ ψ, h => by
      simp only [Semiformula.open_and] at h
      simp [bnd, bnd_open φ h.1, bnd_open ψ h.2]
  | _, φ ⋎ ψ, h => by
      simp only [Semiformula.open_or] at h
      simp [bnd, bnd_open φ h.1, bnd_open ψ h.2]
  | _, ∀⁰ _, h => by simp at h
  | _, ∃⁰ _, h => by simp at h

theorem positive_castLE {n m : ℕ} (h : n + 1 ≤ m + 1) :
    ∀ t : ArithmeticSemiterm ξ (n + 1), t.Positive → (Rew.castLE h t).Positive
  | #x, ht => by
      rw [Rew.castLe_bvar, Semiterm.Positive.bvar]
      rw [Semiterm.Positive.bvar] at ht
      exact ht
  | &x, _ => by simp
  | .func f v, ht => by
      simp only [Semiterm.Positive.func] at ht
      simp only [Rew.func, Semiterm.Positive.func]
      exact fun i => positive_castLE h (v i) (ht i)

theorem bnd_ball {n : ℕ} (ψ φ : ArithmeticSemiformula ξ (n + 1)) (hψ : ψ.Open) :
    bnd (∀⁰[ψ] φ) = ∀⁰[Rew.castLE (Nat.le_succ (n + 1)) ▹ ψ] bnd φ := by
  simp only [FirstOrder.ball, Semiformula.imp_eq, bnd,
    bnd_open (∼ψ) (by simpa using hψ), LogicalConnective.HomClass.map_neg]

theorem bnd_bexs {n : ℕ} (ψ φ : ArithmeticSemiformula ξ (n + 1)) (hψ : ψ.Open) :
    bnd (∃⁰[ψ] φ) =
      ∃⁰[“x. x < !!(lastVar (ξ := ξ) n)”] ((Rew.castLE (Nat.le_succ (n + 1)) ▹ ψ) ⋏ bnd φ) := by
  simp only [FirstOrder.bexs, bnd, bnd_open ψ hψ]

/-- **For `Σ₁` formulas `bnd φ` is `Σ₀`.** -/
theorem hierarchy_bnd {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemiformula ξ n}
    (h : Hierarchy Γ s φ) : s ≤ 1 → (s = 1 → Γ = 𝚺) → Hierarchy 𝚺 0 (bnd φ) := by
  induction h with
  | verum => intros; simp [bnd]
  | falsum => intros; simp [bnd]
  | rel => intros; exact Hierarchy.rew _ (Hierarchy.rel _ _ _ _)
  | nrel => intros; exact Hierarchy.rew _ (Hierarchy.nrel _ _ _ _)
  | and _ _ ih₁ ih₂ => intro hs hΓ; exact Hierarchy.and (ih₁ hs hΓ) (ih₂ hs hΓ)
  | or _ _ ih₁ ih₂ => intro hs hΓ; exact Hierarchy.or (ih₁ hs hΓ) (ih₂ hs hΓ)
  | @ball Γ s n φ t ht _ ih =>
      intro hs hΓ
      rw [bnd_ball _ _ (by simp)]
      have hpos := positive_castLE (Nat.le_succ (n + 1)) t ht
      simpa [hpos] using ih hs hΓ
  | @bexs Γ s n φ t ht _ ih =>
      intro hs hΓ
      rw [bnd_bexs _ _ (by simp), Hierarchy.bexs_iff (lastVar_positive n)]
      exact Hierarchy.and (Hierarchy.rew _ (by simp)) (ih hs hΓ)
  | @exs s n φ _ ih =>
      intro hs _
      simpa [bnd, Hierarchy.bexs_iff (lastVar_positive n)] using ih hs (fun _ => rfl)
  | @all s n φ _ _ => intro hs hΓ; cases hΓ (by omega)
  | @sigma s n φ _ ih =>
      intro hs _
      simpa [bnd, Hierarchy.bexs_iff (lastVar_positive n)] using ih (by omega) (fun h => by omega)
  | @pi s n φ _ _ => intro hs hΓ; cases hΓ (by omega)
  | dummy_sigma => intro hs; omega
  | dummy_pi => intro hs; omega

section semantics

variable {M : Type*} [ORingStructure M]

omit [ORingStructure M] in
theorem snoc_castLE {n : ℕ} (e : Fin n → M) (w : M) :
    (fun x : Fin n => (Fin.snoc e w : Fin (n + 1) → M) (x.castLE (Nat.le_succ n))) = e := by
  funext x
  simp only [Fin.snoc, Fin.val_castLE, x.isLt, dite_true]
  rfl

omit [ORingStructure M] in
theorem cons_snoc {n : ℕ} (x : M) (e : Fin n → M) (w : M) :
    (x :> (Fin.snoc e w : Fin (n + 1) → M)) = Fin.snoc (x :> e) w :=
  Fin.cons_snoc_eq_snoc_cons x e w

theorem val_lastVar {n : ℕ} (x : M) (e : Fin n → M) (w : M) (f : ξ → M) :
    (lastVar (ξ := ξ) n).val (x :> (Fin.snoc e w : Fin (n + 1) → M)) f = w := by
  simp only [lastVar, Semiterm.val_bvar]
  rw [← Fin.succ_last, Matrix.cons_val_succ, Fin.snoc_last]

theorem eval_bnd_atom {n : ℕ} (φ : ArithmeticSemiformula ξ n) (e : Fin n → M) (w : M)
    (f : ξ → M) :
    (Rew.castLE (Nat.le_succ n) ▹ φ).Eval (Fin.snoc e w : Fin (n + 1) → M) f ↔ φ.Eval e f := by
  rw [Semiformula.eval_castLE, snoc_castLE]

/-- **`bnd φ` implies `φ`**, in every structure. -/
theorem eval_bnd_imp : ∀ {n : ℕ} (φ : ArithmeticSemiformula ξ n) (e : Fin n → M) (w : M)
    (f : ξ → M), (bnd φ).Eval (Fin.snoc e w) f → φ.Eval e f
  | _, ⊤, _, _, _, _ => trivial
  | _, ⊥, _, _, _, h => h
  | _, .rel r v, e, w, f, h => (eval_bnd_atom (.rel r v) e w f).mp h
  | _, .nrel r v, e, w, f, h => (eval_bnd_atom (.nrel r v) e w f).mp h
  | _, φ ⋏ ψ, e, w, f, h => by
      simp only [bnd, LogicalConnective.HomClass.map_and] at h ⊢
      exact ⟨eval_bnd_imp φ e w f h.1, eval_bnd_imp ψ e w f h.2⟩
  | _, φ ⋎ ψ, e, w, f, h => by
      simp only [bnd, LogicalConnective.HomClass.map_or] at h ⊢
      exact h.imp (eval_bnd_imp φ e w f) (eval_bnd_imp ψ e w f)
  | _, ∀⁰ φ, e, w, f, h => by
      simp only [bnd, Semiformula.eval_all] at h ⊢
      intro x
      have hx := h x
      rw [cons_snoc] at hx
      exact eval_bnd_imp φ (x :> e) w f hx
  | n, ∃⁰ φ, e, w, f, h => by
      simp only [bnd, Semiformula.eval_bexs, Semiformula.eval_ex] at h ⊢
      obtain ⟨x, -, hx⟩ := h
      rw [cons_snoc] at hx
      exact ⟨x, eval_bnd_imp φ (x :> e) w f hx⟩

end semantics

section monotone

variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

/-- **`bnd φ` is monotone in its bound.** -/
theorem eval_bnd_mono : ∀ {n : ℕ} (φ : ArithmeticSemiformula ξ n) (e : Fin n → M) {w w' : M}
    (f : ξ → M), w ≤ w' → (bnd φ).Eval (Fin.snoc e w) f → (bnd φ).Eval (Fin.snoc e w') f
  | _, ⊤, _, _, _, _, _, _ => trivial
  | _, ⊥, _, _, _, _, _, h => h
  | _, .rel r v, e, w, w', f, _, h =>
      (eval_bnd_atom (.rel r v) e w' f).mpr ((eval_bnd_atom (.rel r v) e w f).mp h)
  | _, .nrel r v, e, w, w', f, _, h =>
      (eval_bnd_atom (.nrel r v) e w' f).mpr ((eval_bnd_atom (.nrel r v) e w f).mp h)
  | _, φ ⋏ ψ, e, _, _, f, hw, h => by
      simp only [bnd, LogicalConnective.HomClass.map_and] at h ⊢
      exact ⟨eval_bnd_mono φ e f hw h.1, eval_bnd_mono ψ e f hw h.2⟩
  | _, φ ⋎ ψ, e, _, _, f, hw, h => by
      simp only [bnd, LogicalConnective.HomClass.map_or] at h ⊢
      exact h.imp (eval_bnd_mono φ e f hw) (eval_bnd_mono ψ e f hw)
  | _, ∀⁰ φ, e, w, w', f, hw, h => by
      simp only [bnd, Semiformula.eval_all] at h ⊢
      intro x
      have hx := h x
      rw [cons_snoc] at hx ⊢
      exact eval_bnd_mono φ (x :> e) f hw hx
  | n, ∃⁰ φ, e, w, w', f, hw, h => by
      simp only [bnd, Semiformula.eval_bexs] at h ⊢
      obtain ⟨x, hxw, hx⟩ := h
      refine ⟨x, ?_, ?_⟩
      · have : x < w := by simpa [val_lastVar] using hxw
        simpa [val_lastVar] using lt_of_lt_of_le this hw
      · rw [cons_snoc] at hx ⊢
        exact eval_bnd_mono φ (x :> e) f hw hx

/-- **An existential witness gives a bound.** -/
theorem eval_bnd_ex {n : ℕ} (φ : ArithmeticSemiformula ξ (n + 1)) (e : Fin n → M) (f : ξ → M)
    (x w : M) (hw : (bnd φ).Eval (Fin.snoc (x :> e) w) f) :
    ∃ w', (bnd (∃⁰ φ)).Eval (Fin.snoc e w') f := by
  refine ⟨max w (x + 1), ?_⟩
  simp only [bnd, Semiformula.eval_bexs]
  refine ⟨x, by simp, ?_⟩
  rw [cons_snoc]
  exact eval_bnd_mono φ (x :> e) f (le_max_left _ _) hw

end monotone

/-! ## Strict induction and collection in models -/

theorem exists_fin_one {α : Type*} {p : (Fin 1 → α) → Prop} : (∃ y, p y) ↔ ∃ b, p ![b] :=
  ⟨fun ⟨y, h⟩ => ⟨y 0, by
    have hy : y = ![y 0] := funext fun i => by rw [Fin.fin_one_eq_zero i]; rfl
    rwa [hy] at h⟩, fun ⟨_, h⟩ => ⟨_, h⟩⟩

section models

variable {M : Type*} [ORingStructure M]
  [hT : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma]

include hT in
theorem models_paMinus : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  Semantics.ModelsSet.of_subset hT Set.subset_union_left

include hT in
theorem models_strict : M↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ StrictSigma :=
  Semantics.ModelsSet.of_subset hT Set.subset_union_right

/-- **Strict induction with model-element parameters.** -/
theorem strict_induction {P : M → Prop} {n : ℕ} (D : Semiformula ℒₒᵣ M (1 + n))
    (hD : Hierarchy 𝚺 0 D)
    (hP : ∀ x, P x ↔ ∃ y : Fin n → M, D.Eval (Matrix.appendr y ![x]) id) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  classical
  haveI : Inhabited M := ⟨0⟩
  haveI := models_strict (M := M)
  refine InductionScheme.succ_induction (C := StrictSigma) (P := P)
    ⟨D.enumarateFVar, ∃⁰^[n] (Rew.rewriteMap D.idxOfFVar ▹ D),
      ⟨n, _, Hierarchy.rew _ hD, rfl⟩, fun x => ?_⟩
  rw [hP x, Semiformula.eval_exsItr]
  simp only [Semiformula.eval_rewriteMap, Semiformula.eval_enumarateFVar_idxOfFVar_eq_id]

/-- **Collection for a monotone `Σ₀` relation.** -/
theorem collection {R : M → M → Prop} (D : Semiformula ℒₒᵣ M 2) (hD : Hierarchy 𝚺 0 D)
    (hR : ∀ x b, R x b ↔ D.Eval ![x, b] id) (mono : ∀ x b c, b ≤ c → R x b → R x c)
    (T : M) (h : ∀ x < T, ∃ b, R x b) : ∃ b, ∀ x < T, R x b := by
  haveI := models_paMinus (M := M)
  let E : Semiformula ℒₒᵣ M (1 + 1) :=
    ∀⁰[“x. x < !!(#2 : Semiterm ℒₒᵣ M 3)”]
      (“x. x < !!(&T : Semiterm ℒₒᵣ M 3)” 🡒 Rew.castLE (by omega) ▹ D)
  have hE : Hierarchy 𝚺 0 E := by
    simp only [E, Hierarchy.ball_iff (by simp : (#2 : Semiterm ℒₒᵣ M 3).Positive)]
    exact Hierarchy.imp_iff.mpr ⟨by simp, Hierarchy.rew _ hD⟩
  have key : ∀ a : M, ∃ b, ∀ x < a, x < T → R x b := by
    refine strict_induction (P := fun a => ∃ b, ∀ x < a, x < T → R x b) (n := 1) E hE ?_ ?_ ?_
    · intro a
      rw [exists_fin_one]
      refine exists_congr fun b => ?_
      simp only [E, Matrix.appendr_cons, Matrix.appendr_nil, Semiformula.eval_ball,
        LogicalConnective.HomClass.map_imply, Semiformula.eval_castLE]
      refine forall_congr' fun x => ?_
      have hx : (fun i : Fin 2 => (x :> ![b, a]) (i.castLE (by omega))) = ![x, b] := by
        funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
      simp [hx, hR]
    · exact ⟨0, fun x hx => absurd hx (by simp)⟩
    · rintro a ⟨b, hb⟩
      obtain ⟨c, hc⟩ : ∃ c, a < T → R a c :=
        if haT : a < T then (h a haT).imp fun _ hc _ => hc else ⟨b, fun h => absurd h haT⟩
      refine ⟨max b c, fun x hx hxT => ?_⟩
      rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hx) with hlt | rfl
      · exact mono x b _ (le_max_left _ _) (hb x hlt hxT)
      · exact mono x c _ (le_max_right _ _) (hc hxT)
  obtain ⟨b, hb⟩ := key T
  exact ⟨b, fun x hx => hb x hx hx⟩

end models

/-! ## Every `Σ₁` formula has the strict form `∃ w, bnd φ` -/

theorem val_positive_cons {n : ℕ} {M : Type*} [ORingStructure M] :
    ∀ (t : ArithmeticSemiterm ξ (n + 1)), t.Positive → ∀ (x y : M) (e : Fin n → M) (f : ξ → M),
      t.val (x :> e) f = t.val (y :> e) f
  | #i, ht, x, y, e, f => by
      rw [Semiterm.Positive.bvar] at ht
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp ht)
      simp
  | &_, _, _, _, _, _ => by simp
  | .func g v, ht, x, y, e, f => by
      rw [Semiterm.Positive.func] at ht
      simp only [Semiterm.val_func]
      congr 1
      funext i
      exact val_positive_cons (v i) (ht i) x y e f

section normal

variable {M : Type*} [ORingStructure M]
  [hT : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma]

/-- The substitution turning the outer bound variables and the free variables
of `bnd φ` (inside one binder) into model parameters. -/
def paramVec {n : ℕ} (e : Fin n → M) : Fin (n + 2) → Semiterm ℒₒᵣ M 2 :=
  Fin.snoc ((#0 : Semiterm ℒₒᵣ M 2) :> fun j => &(e j)) #1

omit hT in
theorem val_paramVec {n : ℕ} (e : Fin n → M) (x b : M) :
    (fun i => (paramVec e i).val ![x, b] id) = (Fin.snoc (x :> e) b : Fin (n + 2) → M) := by
  funext i
  refine Fin.lastCases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i <;>
    simp [paramVec]

include hT in
/-- **A `Σ₁` formula implies its bounded form at some bound.** -/
theorem eval_bnd_of {Γ : Polarity} {s n : ℕ} {φ : ArithmeticSemiformula ξ n}
    (h : Hierarchy Γ s φ) : s ≤ 1 → (s = 1 → Γ = 𝚺) →
      ∀ (e : Fin n → M) (f : ξ → M), φ.Eval e f → ∃ w, (bnd φ).Eval (Fin.snoc e w) f := by
  haveI := models_paMinus (M := M)
  induction h with
  | verum => intros; exact ⟨0, by simp [bnd]⟩
  | falsum => intro _ _ _ _ h; exact h.elim
  | rel => intro _ _ e f h; exact ⟨0, (eval_bnd_atom _ e 0 f).mpr h⟩
  | nrel => intro _ _ e f h; exact ⟨0, (eval_bnd_atom _ e 0 f).mpr h⟩
  | @and Γ s n φ ψ _ _ ih₁ ih₂ =>
      intro hs hΓ e f h
      simp only [LogicalConnective.HomClass.map_and] at h
      obtain ⟨w₁, h₁⟩ := ih₁ hs hΓ e f h.1
      obtain ⟨w₂, h₂⟩ := ih₂ hs hΓ e f h.2
      refine ⟨max w₁ w₂, ?_⟩
      simp only [bnd, LogicalConnective.HomClass.map_and]
      exact ⟨eval_bnd_mono φ e f (le_max_left _ _) h₁, eval_bnd_mono ψ e f (le_max_right _ _) h₂⟩
  | @or Γ s n φ ψ _ _ ih₁ ih₂ =>
      intro hs hΓ e f h
      simp only [LogicalConnective.HomClass.map_or] at h
      rcases h with h | h
      · obtain ⟨w, hw⟩ := ih₁ hs hΓ e f h
        exact ⟨w, by simp only [bnd, LogicalConnective.HomClass.map_or]; exact Or.inl hw⟩
      · obtain ⟨w, hw⟩ := ih₂ hs hΓ e f h
        exact ⟨w, by simp only [bnd, LogicalConnective.HomClass.map_or]; exact Or.inr hw⟩
  | @ball Γ s n φ t ht hφ ih =>
      intro hs hΓ e f h
      simp only [Semiformula.eval_ball] at h
      let T : M := t.val (0 :> e) f
      have hTv : ∀ x : M, t.val (x :> e) f = T := fun x => val_positive_cons t ht x 0 e f
      have hx : ∀ x < T, ∃ b, (bnd φ).Eval (Fin.snoc (x :> e) b) f := fun x hxT =>
        ih hs hΓ (x :> e) f (h x (by simpa [hTv] using hxT))
      let D : Semiformula ℒₒᵣ M 2 := Rew.bind (paramVec e) (fun j => &(f j)) ▹ bnd φ
      have hD : Hierarchy 𝚺 0 D := Hierarchy.rew _ (hierarchy_bnd hφ hs hΓ)
      obtain ⟨b, hb⟩ := collection (R := fun x b => (bnd φ).Eval (Fin.snoc (x :> e) b) f) D hD
        (fun x b => by simp [D, Semiformula.eval_rew, Function.comp_def, val_paramVec])
        (fun x b c hbc => eval_bnd_mono φ (x :> e) f hbc) T hx
      refine ⟨b, ?_⟩
      rw [bnd_ball _ _ (by simp)]
      simp only [Semiformula.eval_ball, Semiformula.eval_castLE]
      intro x hxt
      rw [cons_snoc] at hxt ⊢
      rw [snoc_castLE] at hxt
      exact hb x (by simpa [hTv] using hxt)
  | @bexs Γ s n φ t ht hφ ih =>
      intro hs hΓ e f h
      obtain ⟨x, hxt, hx⟩ := Semiformula.eval_bexs.mp h
      obtain ⟨w, hw⟩ := ih hs hΓ (x :> e) f hx
      refine eval_bnd_ex (“x. x < !!t” ⋏ φ) e f x w ?_
      simp only [bnd, LogicalConnective.HomClass.map_and, bnd_open _ (by simp : (“x. x < !!t” :
        ArithmeticSemiformula ξ (n + 1)).Open), eval_bnd_atom]
      exact ⟨hxt, hw⟩
  | @exs s n φ hφ ih =>
      intro hs _ e f h
      obtain ⟨x, hx⟩ := Semiformula.eval_ex.mp h
      obtain ⟨w, hw⟩ := ih hs (fun _ => rfl) (x :> e) f hx
      exact eval_bnd_ex φ e f x w hw
  | @all s n φ _ _ => intro hs hΓ; cases hΓ (by omega)
  | @sigma s n φ hφ ih =>
      intro hs _ e f h
      obtain ⟨x, hx⟩ := Semiformula.eval_ex.mp h
      obtain ⟨w, hw⟩ := ih (by omega) (fun h => by omega) (x :> e) f hx
      exact eval_bnd_ex φ e f x w hw
  | @pi s n φ _ _ => intro hs hΓ; cases hΓ (by omega)
  | dummy_sigma => intro hs; omega
  | dummy_pi => intro hs; omega

include hT in
/-- **Models of strict induction satisfy `𝗜𝚺₁`.** -/
theorem models_isigma1 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := by
  haveI := models_paMinus (M := M)
  refine Semantics.ModelsSet.union_iff.mpr ⟨?_, ?_⟩
  · exact inferInstance
  · simp only [InductionScheme, Semantics.ModelsSet.setOf_iff, forall_exists_index, and_imp]
    rintro _ φ hφ rfl
    suffices ∀ f : ℕ → M, φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
        ∀ x, φ.Eval ![x] f by
      simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_rew_q,
        Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton] using this
    intro f h0 hs
    let D : Semiformula ℒₒᵣ M (1 + 1) := Rew.bind ![#1, #0] (fun j => &(f j)) ▹ bnd φ
    have hD : Hierarchy 𝚺 0 D := Hierarchy.rew _ (hierarchy_bnd hφ le_rfl (fun _ => rfl))
    refine strict_induction (P := fun x => φ.Eval ![x] f) (n := 1) D hD (fun x => ?_) h0 hs
    have hv : ∀ b : M, (fun i => ((![#1, #0] : Fin 2 → Semiterm ℒₒᵣ M 2) i).val ![b, x] id) =
        ![x, b] := fun b => by
      funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hD : ∀ b : M, D.Eval ![b, x] id ↔ (bnd φ).Eval ![x, b] f := fun b => by
      simp [D, Semiformula.eval_rew, Function.comp_def, hv]
    rw [exists_fin_one]
    constructor
    · intro hx
      obtain ⟨w, hw⟩ := eval_bnd_of hφ le_rfl (fun _ => rfl) ![x] f hx
      refine ⟨w, ?_⟩
      simp only [Matrix.appendr_cons, Matrix.appendr_nil]
      exact (hD w).mpr (by simpa using hw)
    · rintro ⟨b, hb⟩
      simp only [Matrix.appendr_cons, Matrix.appendr_nil] at hb
      exact eval_bnd_imp φ ![x] b f (by simpa using (hD b).mp hb)

end normal

/-- **Strict induction proves every `𝗜𝚺₁` theorem.** -/
theorem isigma1_provable {σ : ArithmeticSentence} (h : 𝗜𝚺₁ ⊢ σ) :
    𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma ⊢ σ := by
  haveI : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma :=
    Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻)
      (Entailment.WeakerThan.ofSubset Set.subset_union_left)
  refine complete.{0} _ σ fun M _ hM => ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_isigma1 (hT := hM)
  exact models_of_provable this h

/-- **`𝗜𝚺₁` is weaker than `𝗣𝗔⁻` plus strict `Σ₁` induction.** -/
instance theory_le : 𝗜𝚺₁ ⪯ 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma :=
  Entailment.weakerThan_iff.mpr fun h => isigma1_provable h

end DiophantineConsistency.StrictSigmaOneInduction
