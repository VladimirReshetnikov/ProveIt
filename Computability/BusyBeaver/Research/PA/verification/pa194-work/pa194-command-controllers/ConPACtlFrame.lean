import ConPACtlWords

/-!
# The frame property of command words

A word that never pops below the stack level at which it starts behaves the same on every
base stack. `follows_exec` states this for the tracked executor: if the run of `W` from a
state `A` does not underflow, the run from any state `B` that differs from `A` only below the
tracked height has the same flag, top and caches, and the same entries above the base.

`Good S W r` says that the tracked run of `W` from the empty store either halts or ends in
the store `⟪r, 0, 0, 0⟫` at height `0`. It is a `𝚺₁` property of `W` and `r`, and `good_run`
transfers it to every base stack and height. `G S r` is `∃ W, Good S W r`.
-/
set_option autoImplicit false
noncomputable section
namespace ConPA.Ctl
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor (cantor first second triangle)

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (S : Sem V)

/-! ## The step on explicit tuples -/

lemma tstep_of_flag (c τ : V) (hf : π₂ (π₂ τ) ≠ 0) : tstep S c τ = τ := by
  simp [tstep, hf]

lemma tstep_final (c σ δ f : V) (hf : f ≠ 0) : tstep S c ⟪σ, δ, f⟫ = ⟪σ, δ, f⟫ :=
  tstep_of_flag S c _ (by simpa using hf)

lemma tstep_shift_halt (y x t w d h δ : V) (hh : S.Halts t h) :
    tstep S ⟪0, y, x⟫ ⟪⟪t, w, d, h⟫, δ, 0⟫ = ⟪⟪t, w, d, h⟫, δ, 1⟫ := by
  unfold Sem.Halts at hh
  simp [tstep, hh]

lemma tstep_shift_under (y x t w d h : V) (hh : ¬S.Halts t h) :
    tstep S ⟪0, y, x⟫ ⟪⟪t, w, d, h⟫, 0, 0⟫ = ⟪⟪t, w, d, h⟫, 0, 2⟫ := by
  unfold Sem.Halts at hh
  simp [tstep, hh]

lemma tstep_shift (y x t w d h δ : V) (hh : ¬S.Halts t h) :
    tstep S ⟪0, y, x⟫ ⟪⟪t, w, d, h⟫, δ + 1, 0⟫ = ⟪⟪h, second w, d, first w⟫, δ, 0⟫ := by
  unfold Sem.Halts at hh
  simp [tstep, hh, S.shift_eq]

lemma tstep_mp_yes (y x t w d h δ : V) (hm : 4 * cantor t (d + y) = h) :
    tstep S ⟪1, y, x⟫ ⟪⟪t, w, d, h⟫, δ, 0⟫ = ⟪mpStore S.mp (d + y) w, δ + (S.up : V), 0⟫ := by
  simp [tstep, hm, S.mp_eq]

lemma tstep_mp_no (y x t w d h δ : V) (hm : 4 * cantor t (d + y) ≠ h) :
    tstep S ⟪1, y, x⟫ ⟪⟪t, w, d, h⟫, δ, 0⟫ = ⟪⟪0, w, d + y, 0⟫, δ, 0⟫ := by
  simp [tstep, hm, S.mp_eq]

lemma tstep_ax (A y x z t w d h δ : V) :
    tstep S ⟪A + 1 + 1, y, x, z⟫ ⟪⟪t, w, d, h⟫, δ, 0⟫ =
      ⟪(if S.ax11 then
          ⟪0, cantor (S.axT (h + y) (d + x) A)
            (stack10 (fun i => S.leaf i (d + x) (h + y) A d) (4 * cantor h (S.genL A d) + 2) t w), z, 0⟫
        else
          ⟪S.axT (h + y) (d + x) A,
            stack10 (fun i => S.leaf i (d + x) (h + y) A d) (4 * cantor h (S.genL A d) + 2) t w, 0, 0⟫),
        δ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (S.g : V), 0⟫ := by
  simp [tstep, S.ax_eq]

lemma texec_of_flag (W τ : V) (hf : π₂ (π₂ τ) ≠ 0) : texec S W τ = τ := by
  induction W using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin c W ih => rw [texec_adjoin, ih, tstep_of_flag S c τ hf]

/-! ## Tracked states -/

scoped notation "stT(" τ ")" => π₁ (π₁ τ)
scoped notation "stW(" τ ")" => π₁ (π₂ (π₁ τ))
scoped notation "stD(" τ ")" => π₁ (π₂ (π₂ (π₁ τ)))
scoped notation "stH(" τ ")" => π₂ (π₂ (π₂ (π₁ τ)))
scoped notation "dep(" τ ")" => π₁ (π₂ τ)
scoped notation "flg(" τ ")" => π₂ (π₂ τ)

lemma state_eta (τ : V) : τ = ⟪⟪stT(τ), stW(τ), stD(τ), stH(τ)⟫, dep(τ), flg(τ)⟫ := by simp

lemma command_eta (c : V) : c = ⟪π₁ c, π₁ (π₂ c), π₂ (π₂ c)⟫ := by simp

/-! ## Stacks that agree above a base -/

/-- The top `δ` entries of `u` and `v` agree, and `v` below them is `v₀`. -/
def SameTop (δ u v v₀ : V) : Prop :=
  (∀ j < δ, first (drop u j) = first (drop v j)) ∧ drop v δ = v₀

lemma sameTop_zero (u v₀ : V) : SameTop 0 u v₀ v₀ :=
  ⟨fun j hj => by simp at hj, by simp⟩

lemma sameTop_push {δ u v v₀ : V} (x : V) (h : SameTop δ u v v₀) :
    SameTop (δ + 1) (cantor x u) (cantor x v) v₀ := by
  refine ⟨?_, by rw [drop_cantor_succ]; exact h.2⟩
  intro j hj
  rcases zero_or_succ j with (rfl | ⟨j, rfl⟩)
  · simp
  · rw [drop_cantor_succ, drop_cantor_succ]
    exact h.1 j (by simpa using hj)

lemma sameTop_pop {δ u v v₀ : V} (h : SameTop (δ + 1) u v v₀) :
    first u = first v ∧ SameTop δ (second u) (second v) v₀ := by
  refine ⟨by simpa only [drop_zero] using h.1 0 (by simp), ?_, ?_⟩
  · intro j hj
    rw [drop_second, drop_second]
    exact h.1 (j + 1) (by simpa using hj)
  · rw [drop_second]
    exact h.2

lemma sameTop_stack10 {δ u v v₀ : V} (f : ℕ → V) (g t : V) (h : SameTop δ u v v₀) :
    SameTop (δ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (stack10 f g t u) (stack10 f g t v) v₀ := by
  unfold stack10
  exact sameTop_push _ (sameTop_push _ (sameTop_push _ (sameTop_push _ (sameTop_push _
    (sameTop_push _ (sameTop_push _ (sameTop_push _ (sameTop_push _ (sameTop_push _ h)))))))))


/-- `B` is `A` on the base `v₀` at the additional height `δ₀`. -/
def Follows (δ₀ v₀ A B : V) : Prop :=
  flg(B) = flg(A) ∧ stT(B) = stT(A) ∧ stD(B) = stD(A) ∧ stH(B) = stH(A) ∧ dep(B) = δ₀ + dep(A) ∧
    SameTop (dep(A)) (stW(A)) (stW(B)) v₀

lemma follows_mk {δ₀ v₀ t u v d h δ f : V} (hs : SameTop δ u v v₀) :
    Follows δ₀ v₀ ⟪⟪t, u, d, h⟫, δ, f⟫ ⟪⟪t, v, d, h⟫, δ₀ + δ, f⟫ := by
  simp [Follows, hs]

lemma follows_iff {δ₀ v₀ t u d h δ f B : V} :
    Follows δ₀ v₀ ⟪⟪t, u, d, h⟫, δ, f⟫ B ↔
      ∃ v, B = ⟪⟪t, v, d, h⟫, δ₀ + δ, f⟫ ∧ SameTop δ u v v₀ := by
  constructor
  · intro hF
    have he := state_eta B
    simp only [Follows, pi₁_pair, pi₂_pair] at hF
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hF
    refine ⟨stW(B), ?_, h6⟩
    rw [h1, h2, h3, h4, h5] at he
    exact he
  · rintro ⟨v, rfl, hs⟩
    exact follows_mk hs

/-- The store after a successful MP, of any of the three kinds, respects the base. -/
lemma follows_mp {δ₀ v₀ δ u v : V} (b : V) (hs : SameTop δ u v v₀) :
    Follows δ₀ v₀ ⟪mpStore S.mp b u, δ + (S.up : V), 0⟫
      ⟪mpStore S.mp b v, δ₀ + (δ + (S.up : V)), 0⟫ := by
  unfold Sem.up mpStore
  cases S.mp
  · have h := follows_mk (δ₀ := δ₀) (t := b) (d := b) (h := (0 : V)) (f := (0 : V))
      (sameTop_push 0 hs)
    simpa using h
  · have h := follows_mk (δ₀ := δ₀) (t := b) (d := b) (h := (0 : V)) (f := (0 : V)) hs
    simpa using h
  · have h := follows_mk (δ₀ := δ₀) (t := (0 : V)) (d := (0 : V)) (h := b) (f := (0 : V)) hs
    simpa using h

/-- The store after AX, in either layout, respects the base. -/
lemma follows_ax {δ₀ v₀ δ u v : V} (T z : V) (f : ℕ → V) (g t : V) (hs : SameTop δ u v v₀) :
    Follows δ₀ v₀
      ⟪(if S.ax11 then ⟪0, cantor T (stack10 f g t u), z, 0⟫ else ⟪T, stack10 f g t u, 0, 0⟫),
        δ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (S.g : V), 0⟫
      ⟪(if S.ax11 then ⟪0, cantor T (stack10 f g t v), z, 0⟫ else ⟪T, stack10 f g t v, 0, 0⟫),
        δ₀ + (δ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (S.g : V)), 0⟫ := by
  unfold Sem.g
  cases S.ax11
  · have h := follows_mk (δ₀ := δ₀) (t := T) (d := (0 : V)) (h := (0 : V)) (f := (0 : V))
      (sameTop_stack10 f g t hs)
    simpa using h
  · have h := follows_mk (δ₀ := δ₀) (t := (0 : V)) (d := z) (h := (0 : V)) (f := (0 : V))
      (sameTop_push T (sameTop_stack10 f g t hs))
    simpa using h

lemma follows_step {δ₀ v₀ A B : V} (c : V) (hf : flg(tstep S c A) ≠ 2)
    (hF : Follows δ₀ v₀ A B) : Follows δ₀ v₀ (tstep S c A) (tstep S c B) := by
  obtain ⟨t, u, d, h, δ, f, rfl⟩ : ∃ t u d h δ f : V, A = ⟪⟪t, u, d, h⟫, δ, f⟫ :=
    ⟨_, _, _, _, _, _, state_eta A⟩
  obtain ⟨v, rfl, hs⟩ := follows_iff.mp hF
  by_cases hfz : f = 0
  · subst hfz
    rw [command_eta c] at hf ⊢
    generalize π₁ (π₂ c) = y at hf ⊢
    generalize π₂ (π₂ c) = x at hf ⊢
    rcases zero_or_succ (π₁ c) with (h0 | ⟨a, ha⟩)
    · rw [h0] at hf ⊢
      by_cases hh : S.Halts t h
      · rw [tstep_shift_halt S y x t u d h δ hh, tstep_shift_halt S y x t v d h (δ₀ + δ) hh]
        exact follows_mk hs
      · rcases zero_or_succ δ with (rfl | ⟨δ', rfl⟩)
        · rw [tstep_shift_under S y x t u d h hh] at hf
          simp at hf
        · rw [tstep_shift S y x t u d h δ' hh, ← add_assoc, tstep_shift S y x t v d h (δ₀ + δ') hh]
          obtain ⟨h1, h2⟩ := sameTop_pop hs
          rw [h1]
          exact follows_mk h2
    · rcases zero_or_succ a with (rfl | ⟨b, rfl⟩)
      · have h1 : π₁ c = 1 := by simpa using ha
        rw [h1] at hf ⊢
        by_cases hm : 4 * cantor t (d + y) = h
        · rw [tstep_mp_yes S y x t u d h δ hm, tstep_mp_yes S y x t v d h (δ₀ + δ) hm, add_assoc]
          exact follows_mp S (d + y) hs
        · rw [tstep_mp_no S y x t u d h δ hm, tstep_mp_no S y x t v d h (δ₀ + δ) hm]
          exact follows_mk hs
      · rw [ha] at hf ⊢
        obtain ⟨x', z, rfl⟩ : ∃ x' z : V, x = ⟪x', z⟫ := ⟨π₁ x, π₂ x, by simp⟩
        rw [tstep_ax S b y x' z t u d h δ, tstep_ax S b y x' z t v d h (δ₀ + δ)]
        have he : δ₀ + δ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (S.g : V) =
            δ₀ + (δ + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (S.g : V)) := by simp [add_assoc]
        rw [he]
        exact follows_ax S _ z _ _ _ hs
  · rw [tstep_final S c _ δ f hfz, tstep_final S c _ (δ₀ + δ) f hfz]
    exact follows_mk hs

lemma one_ne_two' : (1 : V) ≠ 2 := ne_of_lt one_lt_two

lemma zero_ne_two' : (0 : V) ≠ 2 := ne_of_lt zero_lt_two

lemma flag_two_step (c A : V) (h : flg(A) = 2) : flg(tstep S c A) = 2 := by
  rw [tstep_of_flag S c A (by rw [h]; exact (zero_ne_two' (V := V)).symm)]
  exact h

/-- **The frame property.** -/
lemma follows_exec {δ₀ v₀ A B : V} (W : V) (hF : Follows δ₀ v₀ A B) :
    flg(texec S W A) = 2 ∨ Follows δ₀ v₀ (texec S W A) (texec S W B) := by
  induction W using adjoin_ISigma1.sigma1_succ_induction
  · unfold Follows SameTop
    definability
  case nil => right; simpa using hF
  case adjoin c W ih =>
    rw [texec_adjoin, texec_adjoin]
    by_cases h2 : flg(tstep S c (texec S W A)) = 2
    · exact Or.inl h2
    · right
      rcases ih with (h | h)
      · exact absurd (flag_two_step S c _ h) h2
      · exact follows_step S c h2 h

/-! ## Words that compute a formula -/

/-- From the empty store the word `W` halts, or it leaves `r` on top of the empty stack. -/
def Good (W r : V) : Prop :=
  flg(texec S W ⟪⟪0, 0, 0, 0⟫, 0, 0⟫) = 1 ∨
    texec S W ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ = ⟪⟪r, 0, 0, 0⟫, 0, 0⟫

/-- Some word computes `r`. -/
def G (r : V) : Prop := ∃ W, Good S W r

instance G_definable : 𝚺₁-Predicate (G S) := by
  unfold G Good
  definability

/-- A good word computes its formula on every base stack and at every height. -/
lemma good_run {W r : V} (hg : Good S W r) (v δ : V) :
    flg(texec S W ⟪⟪0, v, 0, 0⟫, δ, 0⟫) = 1 ∨
      texec S W ⟪⟪0, v, 0, 0⟫, δ, 0⟫ = ⟪⟪r, v, 0, 0⟫, δ, 0⟫ := by
  have h0 : Follows δ v ⟪⟪0, 0, 0, 0⟫, 0, 0⟫ ⟪⟪0, v, 0, 0⟫, δ, 0⟫ := by
    have h := follows_mk (δ₀ := δ) (t := 0) (d := 0) (h := 0) (f := 0) (sameTop_zero 0 v)
    simpa using h
  rcases follows_exec S W h0 with (h2 | hF)
  · rcases hg with (h1 | he)
    · exact absurd (h1.symm.trans h2) one_ne_two'
    · rw [he] at h2
      simp at h2
  · rcases hg with (h1 | he)
    · left
      rw [hF.1]
      exact h1
    · right
      rw [he] at hF
      obtain ⟨v', hB, hs⟩ := follows_iff.mp hF
      have hv : v' = v := by simpa using hs.2
      rw [hB, hv]
      simp

end model
end ConPA.Ctl
