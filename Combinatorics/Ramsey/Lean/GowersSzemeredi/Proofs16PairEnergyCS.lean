import GowersSzemeredi.Proofs16Lemma19Selection

/-! The Cauchy–Schwarz step of [49] Lemma 19: from two new points to four.

In arXiv:2109.03093, Lemma 19, the witnesses force only two of a quadruple's
four points into the set `A′` of new values. Respected quadruples entirely
inside `A′` are then recovered by Cauchy–Schwarz. Group pairs `(a, c)` by
their key `(a − c, f a − f c)`.

* `pairEnergy S T f` counts pairs-of-pairs `(u, v) ∈ S × T` with equal keys.
* `pairEnergy_eq_sum`: it is `Σ_κ |S_κ|·|T_κ|` over the fibres of the key.
* `pairEnergy_sq_le`: Cauchy–Schwarz,
  `pairEnergy S T² ≤ pairEnergy S S · pairEnergy T T`.
* `pairEnergy_univ_le`: over all pairs, `pairEnergy ≤ N³`, since each fibre
  has at most `N` pairs and the fibres partition `N²` pairs.
* `pairEnergy_self_eq_phiAdditiveCount`: on `A′ × A′` it is exactly the number
  of respected additive quadruples in `A′`.

`two_new_points_energy`: if `X` pairs-of-pairs match between all pairs and
`A′ × A′`, then `f` respects at least `X²/N³` quadruples inside `A′`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The key of a pair: its difference and the difference of its values. -/
def pairKey {N : Nat} (f : ZMod N → ZMod N) (p : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (p.1 - p.2, f p.1 - f p.2)

/-- Pairs-of-pairs with equal keys. -/
def pairEnergy {N : Nat} [NeZero N] (S T : Finset (ZMod N × ZMod N)) (f : ZMod N → ZMod N) : Nat :=
  ((S ×ˢ T).filter fun uv => pairKey f uv.1 = pairKey f uv.2).card

/-- The key fibre of a set of pairs. -/
def keyFibre {N : Nat} [NeZero N] (S : Finset (ZMod N × ZMod N)) (f : ZMod N → ZMod N)
    (κ : ZMod N × ZMod N) : Finset (ZMod N × ZMod N) :=
  S.filter fun p => pairKey f p = κ

theorem pairEnergy_eq_sum {N : Nat} [NeZero N] (S T : Finset (ZMod N × ZMod N)) (f : ZMod N → ZMod N) :
    pairEnergy S T f = ∑ κ, (keyFibre S f κ).card * (keyFibre T f κ).card := by
  unfold pairEnergy keyFibre
  rw [Finset.card_filter, Finset.sum_product]
  have : ∀ u ∈ S, (∑ v ∈ T, if pairKey f u = pairKey f v then 1 else 0) =
      (T.filter fun p => pairKey f p = pairKey f u).card := by
    intro u _
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : pairKey f u = pairKey f v
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  rw [Finset.sum_congr rfl this]
  rw [← Finset.sum_fiberwise S (pairKey f)]
  apply Finset.sum_congr rfl
  intro κ _
  rw [Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.mp hu).2]]
  rw [Finset.sum_const, smul_eq_mul]

/-- **Cauchy–Schwarz for pair energies.** -/
theorem pairEnergy_sq_le {N : Nat} [NeZero N] (S T : Finset (ZMod N × ZMod N)) (f : ZMod N → ZMod N) :
    (pairEnergy S T f) ^ 2 ≤ pairEnergy S S f * pairEnergy T T f := by
  rw [pairEnergy_eq_sum, pairEnergy_eq_sum, pairEnergy_eq_sum]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun κ => (keyFibre S f κ).card) (fun κ => (keyFibre T f κ).card)
  simpa only [sq] using h

/-- Over all pairs the pair energy is at most `N³`. -/
theorem pairEnergy_univ_le {N : Nat} [NeZero N] (f : ZMod N → ZMod N) :
    pairEnergy (Finset.univ : Finset (ZMod N × ZMod N)) Finset.univ f ≤ N ^ 3 := by
  rw [pairEnergy_eq_sum]
  -- each fibre has at most `N` pairs: the first coordinate determines the second
  have hfib : ∀ κ, (keyFibre (Finset.univ : Finset (ZMod N × ZMod N)) f κ).card ≤ N := by
    intro κ
    calc (keyFibre Finset.univ f κ).card
        ≤ ((keyFibre Finset.univ f κ).image Prod.fst).card := by
          apply le_of_eq
          symm
          apply Finset.card_image_of_injOn
          intro p hp q hq hpq
          have h1 := (Finset.mem_filter.mp hp).2
          have h2 := (Finset.mem_filter.mp hq).2
          have hd : p.1 - p.2 = q.1 - q.2 := by
            have := congrArg Prod.fst (h1.trans h2.symm)
            simpa [pairKey] using this
          have hfst : p.1 = q.1 := hpq
          ext
          · exact hfst
          · have : p.2 = p.1 - (p.1 - p.2) := by ring
            rw [this, hd, hfst]; ring
      _ ≤ (Finset.univ : Finset (ZMod N)).card := Finset.card_le_univ _
      _ = N := ZMod.card N
  have htotal : ∑ κ, (keyFibre (Finset.univ : Finset (ZMod N × ZMod N)) f κ).card = N * N := by
    unfold keyFibre
    rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (pairKey f x))]
    simp [ZMod.card]
  calc ∑ κ, (keyFibre Finset.univ f κ).card * (keyFibre Finset.univ f κ).card
      ≤ ∑ κ, N * (keyFibre Finset.univ f κ).card :=
        Finset.sum_le_sum fun κ _ => Nat.mul_le_mul_right _ (hfib κ)
    _ = N * (N * N) := by rw [← Finset.mul_sum, htotal]
    _ = N ^ 3 := by ring

/-- On `A′ × A′` the pair energy counts respected additive quadruples. -/
theorem pairEnergy_self_eq_phiAdditiveCount {N : Nat} [NeZero N] (A : Finset (ZMod N))
    (f : ZMod N → ZMod N) :
    pairEnergy (A ×ˢ A) (A ×ˢ A) f = phiAdditiveCount A f := by
  unfold pairEnergy phiAdditiveCount countWhere
  -- `((a, c), (b, d)) ↦ ![a, d, b, c]`
  apply Finset.card_bij (fun uv _ => (![uv.1.1, uv.2.2, uv.2.1, uv.1.2] : Fin 4 → ZMod N))
  · intro uv huv
    obtain ⟨hmem, hkey⟩ := Finset.mem_filter.mp huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hmem
    obtain ⟨hu1, hu2⟩ := Finset.mem_product.mp hu
    obtain ⟨hv1, hv2⟩ := Finset.mem_product.mp hv
    simp only [pairKey, Prod.mk.injEq] at hkey
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> simpa
    · show uv.1.1 + uv.2.2 = uv.2.1 + uv.1.2
      linear_combination hkey.1
    · show f uv.1.1 + f uv.2.2 = f uv.2.1 + f uv.1.2
      linear_combination hkey.2
  · intro uv _ uv' _ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    simp at h0 h1 h2 h3
    ext <;> simp_all
  · intro q hq
    obtain ⟨_, hmem, hadd, hfadd⟩ := Finset.mem_filter.mp hq
    have hadd' : q 0 + q 1 = q 2 + q 3 := hadd
    refine ⟨((q 0, q 3), (q 2, q 1)), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hmem 0, hmem 3⟩,
        Finset.mem_product.mpr ⟨hmem 2, hmem 1⟩⟩, ?_⟩
      simp only [pairKey, Prod.mk.injEq]
      exact ⟨by linear_combination hadd', by linear_combination hfadd⟩
    · funext i
      fin_cases i <;> rfl

/-- **Two new points suffice.** -/
theorem two_new_points_energy {N : Nat} [NeZero N] (A' : Finset (ZMod N)) (f : ZMod N → ZMod N) :
    (pairEnergy Finset.univ (A' ×ˢ A') f) ^ 2 ≤ N ^ 3 * phiAdditiveCount A' f := by
  calc (pairEnergy Finset.univ (A' ×ˢ A') f) ^ 2
      ≤ pairEnergy Finset.univ Finset.univ f * pairEnergy (A' ×ˢ A') (A' ×ˢ A') f :=
        pairEnergy_sq_le _ _ f
    _ ≤ N ^ 3 * phiAdditiveCount A' f := by
        rw [pairEnergy_self_eq_phiAdditiveCount]
        exact Nat.mul_le_mul_right _ (pairEnergy_univ_le f)

/-- Regrouping pairs-of-pairs: matching keys of `(u, v), (u', v')` is the same as
matching keys of `(v, v'), (u, u')`. -/
theorem pairEnergy_regroup {N : Nat} [NeZero N] (P : ZMod N × ZMod N → ZMod N × ZMod N → Prop)
    [DecidablePred fun uv : (ZMod N × ZMod N) × (ZMod N × ZMod N) => P uv.1 uv.2]
    (f : ZMod N → ZMod N) :
    ((Finset.univ.filter fun uv : (ZMod N × ZMod N) × (ZMod N × ZMod N) =>
        P uv.1 uv.2 ∧ pairKey f uv.1 = pairKey f uv.2)).card =
      ((Finset.univ.filter fun uv : (ZMod N × ZMod N) × (ZMod N × ZMod N) =>
        P (uv.2.1, uv.1.1) (uv.2.2, uv.1.2) ∧ pairKey f uv.1 = pairKey f uv.2)).card := by
  apply Finset.card_bij (fun uv _ => ((uv.1.2, uv.2.2), (uv.1.1, uv.2.1)))
  · intro uv huv
    obtain ⟨hP, hk⟩ := (Finset.mem_filter.mp huv).2
    simp only [pairKey, Prod.mk.injEq] at hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact hP
    · simp only [pairKey, Prod.mk.injEq]
      exact ⟨by linear_combination -hk.1, by linear_combination -hk.2⟩
  · intro uv _ uv' _ h
    simp only [Prod.mk.injEq] at h
    ext <;> simp_all
  · intro uv huv
    obtain ⟨hP, hk⟩ := (Finset.mem_filter.mp huv).2
    simp only [pairKey, Prod.mk.injEq] at hk
    refine ⟨((uv.2.1, uv.1.1), (uv.2.2, uv.1.2)), ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP, ?_⟩
    simp only [pairKey, Prod.mk.injEq]
    exact ⟨by linear_combination -hk.1, by linear_combination -hk.2⟩

/-- Pair energy as a filter over all pairs-of-pairs. -/
theorem pairEnergy_eq_filter {N : Nat} [NeZero N] (S T : Finset (ZMod N × ZMod N))
    (f : ZMod N → ZMod N) :
    pairEnergy S T f = (Finset.univ.filter fun uv : (ZMod N × ZMod N) × (ZMod N × ZMod N) =>
      (uv.1 ∈ S ∧ uv.2 ∈ T) ∧ pairKey f uv.1 = pairKey f uv.2).card := by
  unfold pairEnergy
  congr 1
  ext uv
  simp [Finset.mem_product]

/-- Pair energy is symmetric. -/
theorem pairEnergy_comm {N : Nat} [NeZero N] (S T : Finset (ZMod N × ZMod N)) (f : ZMod N → ZMod N) :
    pairEnergy S T f = pairEnergy T S f := by
  rw [pairEnergy_eq_sum, pairEnergy_eq_sum]
  exact Finset.sum_congr rfl fun κ _ => Nat.mul_comm _ _

/-- **One new point in each pair also suffices**, after two Cauchy–Schwarz
rounds. This handles the mixed cases of [49] Lemma 19. -/
theorem one_new_each_energy {N : Nat} [NeZero N] (A' : Finset (ZMod N)) (f : ZMod N → ZMod N) :
    (pairEnergy (Finset.univ.filter fun p : ZMod N × ZMod N => p.1 ∈ A')
      (Finset.univ.filter fun p : ZMod N × ZMod N => p.2 ∈ A') f) ^ 2 ≤
      N ^ 3 * phiAdditiveCount A' f := by
  set S₁ := Finset.univ.filter fun p : ZMod N × ZMod N => p.1 ∈ A'
  set S₂ := Finset.univ.filter fun p : ZMod N × ZMod N => p.2 ∈ A'
  have h1 : pairEnergy S₁ S₁ f = pairEnergy Finset.univ (A' ×ˢ A') f := by
    rw [pairEnergy_eq_filter S₁ S₁, pairEnergy_eq_filter Finset.univ (A' ×ˢ A'),
      pairEnergy_regroup (fun u v => u ∈ S₁ ∧ v ∈ S₁) f]
    congr 1
    ext uv
    simp [S₁, Finset.mem_product]
  have h2 : pairEnergy S₂ S₂ f = pairEnergy Finset.univ (A' ×ˢ A') f := by
    rw [pairEnergy_comm Finset.univ (A' ×ˢ A'), pairEnergy_eq_filter S₂ S₂,
      pairEnergy_eq_filter (A' ×ˢ A') Finset.univ,
      pairEnergy_regroup (fun u v => u ∈ S₂ ∧ v ∈ S₂) f]
    congr 1
    ext uv
    simp [S₂, Finset.mem_product]
  calc (pairEnergy S₁ S₂ f) ^ 2 ≤ pairEnergy S₁ S₁ f * pairEnergy S₂ S₂ f := pairEnergy_sq_le _ _ f
    _ = (pairEnergy Finset.univ (A' ×ˢ A') f) ^ 2 := by rw [h1, h2, sq]
    _ ≤ N ^ 3 * phiAdditiveCount A' f := two_new_points_energy A' f

end LeanProofs.GowersSzemeredi
