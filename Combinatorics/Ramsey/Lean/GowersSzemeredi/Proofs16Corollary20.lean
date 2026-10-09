import GowersSzemeredi.Proofs16Corollary20Step

/-! [49] Corollary 20 in `ℤ/N`: the iteration.

`corollary20_step` adds a Freiman piece while at least `εN³` distinct
triples are bad. The potential `Σ_x |cov(x)|` starts at `N`, since every
`cov(x) = {0}` for the empty family. It never exceeds `K·N`, because
`cov(x) ⊆ U_x`. Each step raises it by at least `|E′| ≥ κN`: every `x ∈ E′`
gains the new value `f(x)` (`potential_snoc`). Hence at most `⌊K/κ⌋ + 1`
steps occur (`corollary20`).

This is [49] Corollary 20 in `ℤ/N`, with polynomial `κ` (Gowers's
Corollary 7.6 replacing Sanders) and maps on arbitrary sub-domains rather
than coset progressions. Step 2 of the bilinear Bogolyubov argument
("Freiman-linear maps from random selection") is complete in this form. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

variable {N : Nat} [NeZero N]

/-- The potential of a family. -/
def covPotential (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) : Nat :=
  ∑ x, (covSet U E L x).card

omit [NeZero N] in
theorem covSet_subset (U : ZMod N → Finset (ZMod N)) (h0 : ∀ x, (0 : ZMod N) ∈ U x) {m : Nat}
    (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N) (x : ZMod N) :
    covSet U E L x ⊆ U x := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact h0 x
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2.2

theorem covPotential_le (U : ZMod N → Finset (ZMod N)) (h0 : ∀ x, (0 : ZMod N) ∈ U x) {K : Nat}
    (hK : ∀ x, (U x).card ≤ K) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) : covPotential U E L ≤ K * N := by
  unfold covPotential
  calc ∑ x, (covSet U E L x).card ≤ ∑ _x : ZMod N, K :=
        Finset.sum_le_sum fun x _ => (Finset.card_le_card (covSet_subset U h0 E L x)).trans (hK x)
    _ = K * N := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]

theorem covPotential_empty (U : ZMod N → Finset (ZMod N)) :
    covPotential U (Fin.elim0 : Fin 0 → Finset (ZMod N)) (Fin.elim0 : Fin 0 → ZMod N → ZMod N) = N := by
  unfold covPotential covSet
  have : ∀ x : ZMod N, (insert (0 : ZMod N) ((Finset.univ.filter fun i : Fin 0 =>
      x ∈ (Fin.elim0 i : Finset (ZMod N)) ∧ (Fin.elim0 i : ZMod N → ZMod N) x ∈ U x).image
      fun i => (Fin.elim0 i : ZMod N → ZMod N) x)).card = 1 := by
    intro x
    have : (Finset.univ.filter fun i : Fin 0 =>
        x ∈ (Fin.elim0 i : Finset (ZMod N)) ∧ (Fin.elim0 i : ZMod N → ZMod N) x ∈ U x) = ∅ := by
      ext i; exact i.elim0
    rw [this, Finset.image_empty]
    rfl
  rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul, mul_one]

omit [NeZero N] in
/-- Adding a piece only enlarges the covered sets. -/
theorem covSet_snoc_superset (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (E' : Finset (ZMod N)) (f : ZMod N → ZMod N) (x : ZMod N) :
    covSet U E L x ⊆ covSet U (Fin.snoc E E' : Fin (m + 1) → Finset (ZMod N))
      (Fin.snoc L f : Fin (m + 1) → ZMod N → ZMod N) x := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact Finset.mem_insert_self _ _
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_insert_of_mem
    refine Finset.mem_image.mpr ⟨Fin.castSucc i, ?_, by simp⟩
    simpa using hi

/-- **The potential grows by the new piece.** -/
theorem potential_snoc (U : ZMod N → Finset (ZMod N)) {m : Nat} (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (E' : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hnew : ∀ x ∈ E', f x ∈ U x ∧ f x ∉ covSet U E L x) :
    covPotential U E L + E'.card ≤
      covPotential U (Fin.snoc E E' : Fin (m + 1) → Finset (ZMod N))
        (Fin.snoc L f : Fin (m + 1) → ZMod N → ZMod N) := by
  have hpt : ∀ x, (covSet U E L x).card + (if x ∈ E' then 1 else 0) ≤
      (covSet U (Fin.snoc E E' : Fin (m + 1) → Finset (ZMod N))
        (Fin.snoc L f : Fin (m + 1) → ZMod N → ZMod N) x).card := by
    intro x
    have hsub := covSet_snoc_superset U E L E' f x
    by_cases hx : x ∈ E'
    · rw [if_pos hx]
      have hfx : f x ∈ covSet U (Fin.snoc E E' : Fin (m + 1) → Finset (ZMod N))
          (Fin.snoc L f : Fin (m + 1) → ZMod N → ZMod N) x := by
        apply Finset.mem_insert_of_mem
        refine Finset.mem_image.mpr ⟨Fin.last m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
        · simpa using hx
        · simpa using (hnew x hx).1
        · simp
      have hins : insert (f x) (covSet U E L x) ⊆ covSet U (Fin.snoc E E' : Fin (m + 1) → Finset (ZMod N))
          (Fin.snoc L f : Fin (m + 1) → ZMod N → ZMod N) x := Finset.insert_subset hfx hsub
      have := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem (hnew x hx).2] at this
      exact this
    · rw [if_neg hx, add_zero]
      exact Finset.card_le_card hsub
  unfold covPotential
  have hcount : (∑ x : ZMod N, if x ∈ E' then 1 else 0) = E'.card := by
    rw [Finset.sum_boole]
    simp
  calc (∑ x, (covSet U E L x).card) + E'.card
      = ∑ x, ((covSet U E L x).card + if x ∈ E' then 1 else 0) := by
        rw [Finset.sum_add_distrib, hcount]
    _ ≤ _ := Finset.sum_le_sum fun x _ => hpt x

/-- **[49] Corollary 20 in `ℤ/N`.** After at most `⌊K/κ⌋ + 1` Freiman pieces,
fewer than `εN³` distinct triples are bad. -/
theorem corollary20 [Fact N.Prime] (U : ZMod N → Finset (ZMod N))
    (h0 : ∀ x, (0 : ZMod N) ∈ U x) {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N),
      m ≤ ⌊(K : Real) / corollary20Kappa ε K⌋₊ + 1 ∧ (∀ i, IsFreimanLinearOn (E i) (L i)) ∧
      ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real) ^ 3 := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hκ : 0 < corollary20Kappa ε K := by
    unfold corollary20Kappa
    have : (1 : Real) ≤ K := by exact_mod_cast hK1
    positivity
  -- the invariant after `s` steps
  have key : ∀ s : Nat, (∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N),
      m ≤ s ∧ (∀ i, IsFreimanLinearOn (E i) (L i)) ∧
      (N : Real) + s * (corollary20Kappa ε K * N) ≤ covPotential U E L) ∨
      (∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N),
      m ≤ s ∧ (∀ i, IsFreimanLinearOn (E i) (L i)) ∧
      ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real) ^ 3) := by
    intro s
    induction s with
    | zero =>
      refine Or.inl ⟨0, Fin.elim0, Fin.elim0, le_rfl, fun i => i.elim0, ?_⟩
      rw [covPotential_empty]
      simp
    | succ s ih =>
      rcases ih with ⟨m, E, L, hm, hF, hP⟩ | ⟨m, E, L, hm, hF, hbad⟩
      · by_cases hbad : ((Finset.univ.filter (IsBadTriple U E L)).card : Real) < ε * (N : Real) ^ 3
        · exact Or.inr ⟨m, E, L, by omega, hF, hbad⟩
        · push Not at hbad
          obtain ⟨f, E', hnew, hcard, hF'⟩ := corollary20_step U h0 hK1 hK E L hε hbad
          refine Or.inl ⟨m + 1, Fin.snoc E E', Fin.snoc L f, by omega, ?_, ?_⟩
          · intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simpa using hF'
            · simpa using hF j
          · have hgrow := potential_snoc U E L E' f hnew
            have hgrowR : (covPotential U E L : Real) + E'.card ≤
                covPotential U (Fin.snoc E E' : Fin (m + 1) → Finset (ZMod N))
                  (Fin.snoc L f : Fin (m + 1) → ZMod N → ZMod N) := by exact_mod_cast hgrow
            push_cast
            linarith
      · exact Or.inr ⟨m, E, L, by omega, hF, hbad⟩
  set s := ⌊(K : Real) / corollary20Kappa ε K⌋₊ + 1
  rcases key s with ⟨m, E, L, hm, hF, hP⟩ | hdone
  · exfalso
    have hle : (covPotential U E L : Real) ≤ K * N := by
      exact_mod_cast covPotential_le U h0 hK E L
    have hs : (K : Real) / corollary20Kappa ε K < s := by
      have := Nat.lt_floor_add_one ((K : Real) / corollary20Kappa ε K)
      simpa [s] using this
    have hsκ : (K : Real) < s * corollary20Kappa ε K := by
      rw [div_lt_iff₀ hκ] at hs
      linarith
    have : (s : Real) * (corollary20Kappa ε K * N) > K * N := by
      have := mul_lt_mul_of_pos_right hsκ hNR
      linarith
    linarith
  · exact hdone

end LeanProofs.GowersSzemeredi
