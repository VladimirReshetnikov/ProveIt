import ConciseIPRA.NativePublic

/-!
# The public language is necessary

`NativePublic` proves that the calculus `PGPrf` (the root-determined
introduction, and transport at iterator sources only) derives the translation
of a sequent into a public language exactly when the kernel derives the
sequent.  This module shows that the translation cannot be dropped:

* `pgprf_not_trans`: `PGPrf` does not derive `x = z` from `x = y` and `y = z`,
  for three variables;
* `pgprf_strictly_weaker`: so on arbitrary sequents `PGPrf` is strictly weaker
  than the kernel.

The proof is a reading of the formulas for which every rule of `PGPrf` is
sound (`PGPrf.sound`) and in which equality is not transitive.  A *value* is
a number with a colour; colour `0` is an ordinary number.  A variable may
hold any value.  A term that is not a variable has an ordinary number as its
value, computed from the numbers of its variables.  Bound variables range
over ordinary numbers.  An equation holds when its two sides have the same
number, or when their colours are adjacent in `1 — 2 — 3`.  So with
`x, y, z` coloured `1, 2, 3` and given different numbers, `x = y` and `y = z`
hold and `x = z` does not.

Transport is sound because its source is an iterator: it has colour `0`, so
the equation `J = t` holds by number, and a template other than the hole
itself cannot see the colour of what is plugged in.  The introduction is
sound because a matrix that holds by colours does not depend on its bound
variables (`Colour.succ_of_H`), so a closure over it holds trivially
(`Colour.T_Q_eq`), and the truth of a compound formula does not depend on the
colours of its free variables (`Colour.T_recolor`).
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n m : ℕ}

namespace Colour

/-- A value: a number and a colour.  Colour `0` is an ordinary number. -/
abbrev V := ℕ × ℕ

/-- Adjacency of the colours `1 — 2 — 3`. -/
def H (c c' : ℕ) : Prop :=
  (c = 1 ∧ c' = 2) ∨ (c = 2 ∧ c' = 1) ∨ (c = 2 ∧ c' = 3) ∨ (c = 3 ∧ c' = 2)

theorem H.symm {c c' : ℕ} (h : H c c') : H c' c := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact .inr (.inl ⟨h₂, h₁⟩)
  · exact .inl ⟨h₂, h₁⟩
  · exact .inr (.inr (.inr ⟨h₂, h₁⟩))
  · exact .inr (.inr (.inl ⟨h₂, h₁⟩))

theorem H.left_ne {c c' : ℕ} (h : H c c') : c ≠ 0 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem H.right_ne {c c' : ℕ} (h : H c c') : c' ≠ 0 := h.symm.left_ne

/-- The meaning of an equation between values: the same number, or adjacent
colours. -/
def E (v w : V) : Prop := v.1 = w.1 ∨ H v.2 w.2

theorem E.symm {v w : V} (h : E v w) : E w v :=
  h.elim (fun e => .inl e.symm) (fun e => .inr e.symm)

/-- The value of a term: a variable has the value it is given, any other term
the ordinary number that it denotes. -/
def tval : {n : ℕ} → Tm n → (Fin n → V) → V
  | _, .var i, ρ => ρ i
  | _, .zero, _ => (0, 0)
  | _, .succ t, ρ => ((Tm.succ t).val .std fun i => (ρ i).1, 0)
  | _, .iter c a h, ρ => ((Tm.iter c a h).val .std fun i => (ρ i).1, 0)

theorem tval_fst (t : Tm n) (ρ : Fin n → V) :
    (tval t ρ).1 = t.val .std fun i => (ρ i).1 := by
  cases t <;> rfl

theorem tval_var_of_snd {t : Tm n} {ρ : Fin n → V} (h : (tval t ρ).2 ≠ 0) :
    ∃ i, t = .var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | zero => exact absurd rfl h
  | succ t => exact absurd rfl h
  | iter c a g => exact absurd rfl h

theorem tval_fst_congr (t : Tm n) {ρ ρ' : Fin n → V} (h : ∀ i, (ρ i).1 = (ρ' i).1) :
    (tval t ρ).1 = (tval t ρ').1 := by
  rw [tval_fst, tval_fst]
  congr 1
  funext i
  exact h i

theorem tval_subst (σ : Fin n → Tm m) (t : Tm n) (ρ : Fin m → V) :
    tval (Syn.subst σ t) ρ = tval t fun i => tval (σ i) ρ := by
  have key : (tval (Syn.subst σ t) ρ).1 = (tval t fun i => tval (σ i) ρ).1 := by
    rw [tval_fst, tval_fst, Tm.val_subst]
    congr 1
    funext i
    rw [tval_fst]
  cases t with
  | var i => rfl
  | zero => rfl
  | succ t => exact Prod.ext key rfl
  | iter c a g => exact Prod.ext key rfl

theorem tval_shift (t : Tm n) (v : V) (ρ : Fin n → V) :
    tval (Syn.shift t) (Fin.cases v ρ) = tval t ρ := by
  unfold Syn.shift
  rw [tval_subst]
  rfl

theorem tval_inst (t : Tm n) (ρ : Fin n → V) :
    (fun i => tval (inst t i) ρ) = Fin.cases (tval t ρ) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Syn.inst_succ, Fin.cases_succ]
    rfl

theorem tval_up (σ : Fin n → Tm m) (v : V) (ρ : Fin m → V) :
    (fun i => tval (up σ i) (Fin.cases v ρ)) = Fin.cases v fun i => tval (σ i) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Syn.up_succ, Fin.cases_succ, tval_shift]

theorem tval_repl (s : Tm (n + 1)) (v : V) (ρ : Fin n → V) :
    (fun i => tval (repl s i) (Fin.cases v ρ)) = Fin.cases (tval s (Fin.cases v ρ)) ρ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Syn.repl_succ, Fin.cases_succ]
    rfl

/-- Two valuations with the same numbers, extended by values with the same
number, have the same numbers. -/
theorem fst_cases {ρ ρ' : Fin n → V} (h : ∀ i, (ρ i).1 = (ρ' i).1) {v w : V} (hv : v.1 = w.1)
    (i : Fin (n + 1)) :
    ((Fin.cases v ρ : Fin (n + 1) → V) i).1 = ((Fin.cases w ρ' : Fin (n + 1) → V) i).1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact h j

/-- Removing the colour of the first value keeps the numbers. -/
theorem fst_cases_fst (w : V) (ρ : Fin n → V) (i : Fin (n + 1)) :
    ((Fin.cases (w.1, 0) ρ : Fin (n + 1) → V) i).1 = ((Fin.cases w ρ : Fin (n + 1) → V) i).1 :=
  fst_cases (v := (w.1, 0)) (w := w) (fun _ => rfl) rfl i

/-- Removing the colour of the second value keeps the numbers. -/
theorem fst_cases_snd (v w : V) (ρ : Fin n → V) (i : Fin (n + 2)) :
    ((Fin.cases v (Fin.cases (w.1, 0) ρ) : Fin (n + 2) → V) i).1
      = ((Fin.cases v (Fin.cases w ρ) : Fin (n + 2) → V) i).1 :=
  fst_cases (v := v) (w := v) (fst_cases_fst w ρ) rfl i

/-- The truth of a formula.  Bound variables range over ordinary numbers. -/
def T : {n : ℕ} → NFm n → (Fin n → V) → Prop
  | _, .eq a b, ρ => E (tval a ρ) (tval b ρ)
  | _, .Q B, ρ => T B (Fin.cases (0, 0) ρ) → ∀ d : ℕ, T B (Fin.cases (d, 0) ρ)
  | _, .D B, ρ => ∃ d : ℕ, T B (Fin.cases (0, 0) (Fin.cases (d, 0) ρ)) →
      ∀ e : ℕ, T B (Fin.cases (e, 0) (Fin.cases (d, 0) ρ))

theorem T_subst (A : NFm n) : ∀ {m : ℕ} (σ : Fin n → Tm m) (ρ : Fin m → V),
    T (A.subst σ) ρ = T A fun i => tval (σ i) ρ := by
  induction A with
  | eq s t => intro m σ ρ; simp only [NFm.subst_eq, T, tval_subst]
  | Q B ih => intro m σ ρ; simp only [NFm.subst_Q, T, ih, tval_up]
  | D B ih => intro m σ ρ; simp only [NFm.subst_D, T, ih, tval_up]

theorem T_shift (A : NFm n) (v : V) (ρ : Fin n → V) : T A.shift (Fin.cases v ρ) = T A ρ := by
  unfold NFm.shift
  rw [T_subst]
  rfl

theorem T_inst (B : NFm (n + 1)) (t : Tm n) (ρ : Fin n → V) :
    T (B.subst (inst t)) ρ = T B (Fin.cases (tval t ρ) ρ) := by
  rw [T_subst, tval_inst]

theorem T_repl (B : NFm (n + 1)) (s : Tm (n + 1)) (v : V) (ρ : Fin n → V) :
    T (B.subst (repl s)) (Fin.cases v ρ) = T B (Fin.cases (tval s (Fin.cases v ρ)) ρ) := by
  rw [T_subst, tval_repl]

theorem T_up_inst (B : NFm (n + 2)) (t : Tm n) (v : V) (ρ : Fin n → V) :
    T (B.subst (up (inst t))) (Fin.cases v ρ)
      = T B (Fin.cases v (Fin.cases (tval t ρ) ρ)) := by
  rw [T_subst, tval_up, tval_inst]

/-- An equation is preserved when values with colour `0` are given a colour:
truth by number is unchanged, and truth by colours only looks at values that
keep their colour. -/
theorem T_eq_mono {a b : Tm n} {ρ ρ' : Fin n → V} (h : ∀ i, (ρ i).1 = (ρ' i).1)
    (hc : ∀ i, (ρ i).2 ≠ 0 → ρ i = ρ' i) (h0 : T (.eq a b) ρ) : T (.eq a b) ρ' := by
  rcases (show E (tval a ρ) (tval b ρ) from h0) with e | e
  · exact .inl (by rw [← tval_fst_congr a h, ← tval_fst_congr b h]; exact e)
  · obtain ⟨i, rfl⟩ := tval_var_of_snd e.left_ne
    obtain ⟨j, rfl⟩ := tval_var_of_snd e.right_ne
    refine .inr ?_
    show H (ρ' i).2 (ρ' j).2
    rw [← hc i e.left_ne, ← hc j e.right_ne]
    exact e

/-- If an equation holds by colours under a valuation whose first value is an
ordinary number, neither side is the first variable. -/
theorem succ_of_H {a b : Tm (n + 1)} {d : ℕ} {σ : Fin n → V}
    (h : H (tval a (Fin.cases (d, 0) σ)).2 (tval b (Fin.cases (d, 0) σ)).2) :
    (∃ p, a = .var (Fin.succ p)) ∧ (∃ q, b = .var (Fin.succ q)) := by
  have key : ∀ x : Tm (n + 1), (tval x (Fin.cases (d, 0) σ)).2 ≠ 0 →
      ∃ p, x = .var (Fin.succ p) := by
    intro x hx
    obtain ⟨i, rfl⟩ := tval_var_of_snd hx
    revert hx
    refine Fin.cases ?_ (fun p => ?_) i
    · intro hx; exact absurd rfl hx
    · intro _; exact ⟨p, rfl⟩
  exact ⟨key a h.left_ne, key b h.right_ne⟩

/-- A closure over a literal equation holds exactly when it holds by number. -/
theorem T_Q_eq (a b : Tm (n + 1)) (ρ : Fin n → V) :
    T (.Q (.eq a b)) ρ ↔
      ((tval a (Fin.cases (0, 0) ρ)).1 = (tval b (Fin.cases (0, 0) ρ)).1 →
        ∀ d : ℕ, (tval a (Fin.cases (d, 0) ρ)).1 = (tval b (Fin.cases (d, 0) ρ)).1) := by
  constructor
  · intro h h0 d
    rcases (show E _ _ from h (.inl h0) d) with e | e
    · exact e
    · obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := succ_of_H e
      exact h0
  · intro h h0 d
    rcases (show E _ _ from h0) with e | e
    · exact .inl (h e d)
    · obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := succ_of_H e
      exact .inr e

/-- The truth of a compound formula does not depend on colours. -/
theorem T_recolor (A : NFm n) : ∀ {ρ ρ' : Fin n → V}, (∀ i, (ρ i).1 = (ρ' i).1) →
    A.isEq = false → (T A ρ ↔ T A ρ') := by
  induction A with
  | eq a b => intro ρ ρ' _ h; exact Bool.noConfusion h
  | Q B ih =>
    intro ρ ρ' h _
    cases B with
    | eq a b =>
      have e : ∀ d : ℕ, ((tval a (Fin.cases (d, 0) ρ)).1 = (tval b (Fin.cases (d, 0) ρ)).1)
          = ((tval a (Fin.cases (d, 0) ρ')).1 = (tval b (Fin.cases (d, 0) ρ')).1) := fun d => by
        rw [tval_fst_congr a (fst_cases h rfl), tval_fst_congr b (fst_cases h rfl)]
      rw [T_Q_eq, T_Q_eq]
      exact imp_congr (by rw [e 0]) (forall_congr' fun d => by rw [e d])
    | Q B' =>
      exact imp_congr (ih (fst_cases h rfl) rfl) (forall_congr' fun d => ih (fst_cases h rfl) rfl)
    | D B' =>
      exact imp_congr (ih (fst_cases h rfl) rfl) (forall_congr' fun d => ih (fst_cases h rfl) rfl)
  | D B ih =>
    intro ρ ρ' h _
    cases B with
    | eq a b =>
      have e : ∀ x d : ℕ,
          ((tval a (Fin.cases (d, 0) (Fin.cases (x, 0) ρ))).1
            = (tval b (Fin.cases (d, 0) (Fin.cases (x, 0) ρ))).1)
          = ((tval a (Fin.cases (d, 0) (Fin.cases (x, 0) ρ'))).1
            = (tval b (Fin.cases (d, 0) (Fin.cases (x, 0) ρ'))).1) := fun x d => by
        rw [tval_fst_congr a (fst_cases (fst_cases h rfl) rfl),
          tval_fst_congr b (fst_cases (fst_cases h rfl) rfl)]
      refine exists_congr fun x => ?_
      show T (.Q (.eq a b)) (Fin.cases (x, 0) ρ) ↔ T (.Q (.eq a b)) (Fin.cases (x, 0) ρ')
      rw [T_Q_eq, T_Q_eq]
      exact imp_congr (by rw [e x 0]) (forall_congr' fun d => by rw [e x d])
    | Q B' =>
      exact exists_congr fun x => imp_congr (ih (fst_cases (fst_cases h rfl) rfl) rfl)
        (forall_congr' fun d => ih (fst_cases (fst_cases h rfl) rfl) rfl)
    | D B' =>
      exact exists_congr fun x => imp_congr (ih (fst_cases (fst_cases h rfl) rfl) rfl)
        (forall_congr' fun d => ih (fst_cases (fst_cases h rfl) rfl) rfl)

/-- A matrix that holds at an ordinary number holds at every value with that
number. -/
theorem T_mono_first (B : NFm (n + 1)) (w : V) (ρ : Fin n → V)
    (h : T B (Fin.cases (w.1, 0) ρ)) : T B (Fin.cases w ρ) := by
  cases B with
  | eq a b =>
    refine T_eq_mono (fst_cases_fst w ρ) (fun i => ?_) h
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hc; exact absurd rfl hc
    · intro _; rfl
  | Q B' =>
    exact (T_recolor _ (fst_cases_fst w ρ) rfl).mp h
  | D B' =>
    exact (T_recolor _ (fst_cases_fst w ρ) rfl).mp h

/-- Colouring the second value preserves an equation. -/
theorem T_eq_mono_second {a b : Tm (n + 2)} (v w : V) (ρ : Fin n → V)
    (h : T (.eq a b) (Fin.cases v (Fin.cases (w.1, 0) ρ))) :
    T (.eq a b) (Fin.cases v (Fin.cases w ρ)) := by
  refine T_eq_mono (fst_cases_snd v w ρ) (fun i => ?_) h
  refine Fin.cases ?_ (fun j => ?_) i
  · intro _; rfl
  · refine Fin.cases ?_ (fun l => ?_) j
    · intro hc; exact absurd rfl hc
    · intro _; rfl

/-- The colour of the second value does not matter for a compound matrix. -/
theorem T_recolor_second (A : NFm (n + 2)) (hA : A.isEq = false) (v w : V) (ρ : Fin n → V) :
    T A (Fin.cases v (Fin.cases (w.1, 0) ρ)) ↔ T A (Fin.cases v (Fin.cases w ρ)) :=
  T_recolor A (fst_cases_snd v w ρ) hA

/-- Removing the colour of the second value of an equation: if it held by
colours, it does not depend on the first value. -/
theorem T_eq_back {a b : Tm (n + 2)} {e : ℕ} {w : V} {ρ : Fin n → V}
    (h : T (.eq a b) (Fin.cases (e, 0) (Fin.cases w ρ)))
    (h0 : T (.eq a b) (Fin.cases (0, 0) (Fin.cases (w.1, 0) ρ))) :
    T (.eq a b) (Fin.cases (e, 0) (Fin.cases (w.1, 0) ρ)) := by
  have hf := fst_cases_snd (e, 0) w ρ
  rcases (show E _ _ from h) with k | k
  · exact .inl (by rw [tval_fst_congr a hf, tval_fst_congr b hf]; exact k)
  · obtain ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩ := succ_of_H k
    exact h0

/-- Transport at a source with colour `0` is sound. -/
theorem tr_sound (h : Tm (n + 1)) {J t : Tm n} {ρ : Fin n → V} {u : V}
    (hJ : (tval J ρ).2 = 0) (h₁ : E (tval J ρ) (tval t ρ))
    (h₂ : E (tval (Syn.subst (inst J) h) ρ) u) : E u (tval (Syn.subst (inst t) h) ρ) := by
  have e₁ : (tval J ρ).1 = (tval t ρ).1 := h₁.elim id fun k => absurd hJ k.left_ne
  have hf : ∀ i, ((Fin.cases (tval J ρ) ρ : Fin (n + 1) → V) i).1
      = ((Fin.cases (tval t ρ) ρ : Fin (n + 1) → V) i).1 := fst_cases (fun _ => rfl) e₁
  rw [tval_subst, tval_inst] at h₂ ⊢
  cases h with
  | var i =>
    revert h₂
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h₂
      have e₂ : (tval J ρ).1 = u.1 := h₂.elim id fun k => absurd hJ k.left_ne
      exact .inl (e₂.symm.trans e₁)
    · intro h₂; exact h₂.symm
  | zero => exact h₂.symm
  | succ c =>
    have e : tval (Tm.succ c) (Fin.cases (tval J ρ) ρ)
        = tval (Tm.succ c) (Fin.cases (tval t ρ) ρ) := Prod.ext (tval_fst_congr _ hf) rfl
    rw [← e]; exact h₂.symm
  | iter c a g =>
    have e : tval (Tm.iter c a g) (Fin.cases (tval J ρ) ρ)
        = tval (Tm.iter c a g) (Fin.cases (tval t ρ) ρ) := Prod.ext (tval_fst_congr _ hf) rfl
    rw [← e]; exact h₂.symm

end Colour

open Colour in
/-- Every rule of `PGPrf` is sound for the reading with colours. -/
theorem PGPrf.sound {Γ : List (NFm n)} {A : NFm n} (h : PGPrf Γ A) :
    ∀ ρ : Fin n → V, (∀ C ∈ Γ, T C ρ) → T A ρ := by
  induction h with
  | hyp h => intro ρ hΓ; exact hΓ _ h
  | iterZero a g =>
    intro ρ _
    refine .inl ?_
    rw [tval_fst, tval_fst]
    exact NPrf.sound_std (Γ := []) (.iterZero a g) _ (fun _ hX => nomatch hX)
  | iterSucc c a g =>
    intro ρ _
    refine .inl ?_
    rw [tval_fst, tval_fst]
    exact NPrf.sound_std (Γ := []) (.iterSucc c a g) _ (fun _ hX => nomatch hX)
  | trI h c a g _ _ ih₁ ih₂ =>
    intro ρ hΓ
    exact tr_sound h rfl (ih₁ ρ hΓ) (ih₂ ρ hΓ)
  | @qE _ Γ B t _ _ ih₁ ih₂ =>
    intro ρ hΓ
    have h0 := ih₂ ρ hΓ
    rw [T_inst] at h0 ⊢
    exact T_mono_first B (tval t ρ) ρ (ih₁ ρ hΓ h0 (tval t ρ).1)
  | @dE _ Γ B A _ _ ih₁ ih₂ =>
    intro ρ hΓ
    obtain ⟨d, hd⟩ := ih₁ ρ hΓ
    have k := ih₂ (Fin.cases (d, 0) ρ) (by
      intro C hC
      rcases List.mem_cons.1 hC with rfl | hC
      · exact hd
      · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
        rw [T_shift]
        exact hΓ _ hC₀)
    rwa [T_shift] at k
  | @dI n Γ B t _ ih =>
    intro ρ hΓ
    have hΓ' : ∀ (e : ℕ), ∀ C ∈ Γ.map NFm.shift, T C (Fin.cases (e, 0) ρ) := by
      intro e C hC
      obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.1 hC
      rw [T_shift]
      exact hΓ _ hC₀
    refine ⟨(tval t ρ).1, fun h0 e => ?_⟩
    cases hB : B.isEq with
    | false =>
      -- a compound matrix: cases, and the colour of the witness does not matter
      have he : NFm.eta B (Syn.var 0 : Tm (n + 1)) = zero := by
        unfold NFm.eta
        rw [hB]
        rfl
      cases e with
      | zero => exact h0
      | succ e =>
        have c := ih (Fin.cases (e, 0) ρ) (by
          intro C hC
          rcases List.mem_cons.1 hC with rfl | hC
          · rw [he, T_repl, T_up_inst]
            exact (T_recolor_second B hB _ _ _).mp h0
          · exact hΓ' e C hC)
        rw [T_repl, T_up_inst] at c
        exact (T_recolor_second B hB _ _ _).mpr c
    | true =>
      -- a literal equation: progress, by induction on the ordinary number
      obtain ⟨a, b, rfl⟩ : ∃ a b, B = NFm.eq a b := by
        cases B with
        | eq a b => exact ⟨a, b, rfl⟩
        | Q B' => cases hB
        | D B' => cases hB
      induction e with
      | zero => exact h0
      | succ e ihe =>
        have m₁ := T_eq_mono_second (e, 0) (tval t ρ) ρ ihe
        have c := ih (Fin.cases (e, 0) ρ) (by
          intro C hC
          rcases List.mem_cons.1 hC with rfl | hC
          · rw [show NFm.eta (NFm.eq a b) (Syn.var 0 : Tm (n + 1)) = Syn.var 0 from rfl,
              NFm.subst_repl_var, T_up_inst]
            exact m₁
          · exact hΓ' e C hC)
        rw [T_repl, T_up_inst] at c
        exact T_eq_back c h0

open Colour in
/-- **Transitivity between variables is not derivable** with the
root-determined introduction and transport at iterator sources only. -/
theorem pgprf_not_trans :
    ¬ PGPrf [NFm.eq (Syn.var 0 : Tm 3) (Syn.var 1), NFm.eq (Syn.var 1) (Syn.var 2)]
      (.eq (Syn.var 0) (Syn.var 2)) := by
  intro h
  have k := h.sound (fun i => ((i : ℕ), (i : ℕ) + 1)) (by
    intro C hC
    rcases List.mem_cons.1 hC with rfl | hC
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · rcases List.mem_cons.1 hC with rfl | hC
      · exact .inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))
      · exact nomatch hC)
  rcases (show (0 : ℕ) = 2 ∨ H 1 3 from k) with e | e
  · exact absurd e (by decide)
  · rcases e with ⟨_, e⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ <;> exact absurd e (by decide)

/-- **The public language is necessary.**  On arbitrary sequents the calculus
`PGPrf` is strictly weaker than the kernel. -/
theorem pgprf_strictly_weaker :
    ∃ (Γ : List (NFm 3)) (A : NFm 3), NPrf Γ A ∧ ¬ PGPrf Γ A :=
  ⟨_, _, NPrf.eqTrans (.hyp List.mem_cons_self)
    (.hyp (List.mem_cons_of_mem _ List.mem_cons_self)), pgprf_not_trans⟩

end LeanProofs.ConciseIPRA
