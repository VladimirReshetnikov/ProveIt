import GowersSzemeredi.Proofs16PairEnergyCS

/-! [49] Lemma 19 in `ℤ/N` in its original shape: two new points.

In arXiv:2109.03093, Lemma 19, a witness quadruple
`(a′, b′, c′, d′) = (y+z, z, y+w, w)` has `a′ − c′ = b′ − d′`, values
`u_{a′} − u_{c′} = u_{b′} − u_{d′}`, all values allowed (`u ∈ U`), and only
`b′, d′` carrying new values (`u ∈ W`). This module proves that form:
* selection averaging (`exists_good_selection`) gives `f` meeting
  `≥ |T|/(256K⁴)` witnesses;
* each met witness is a pair-of-pairs `((a′, c′), (b′, d′))` with equal keys,
  with `(b′, d′) ∈ A′ × A′` and `A′ = {f y ∈ W y}`;
* Cauchy–Schwarz (`two_new_points_energy`) turns `X ≥ δN³` such matches into
  `≥ δ²N³` respected quadruples inside `A′`;
* `lineFreimanExtraction_holds` (Gowers's Corollary 7.6) gives the Freiman
  piece, of size `≥ 2^(−1882)(δ²)^1164·N`.

`lemma19_two_new_piece` therefore replaces `lemma19_selection_piece`, whose
four-new-points hypothesis is stronger than [49] provides.

`lemma19_mixed_piece` covers [49]'s mixed cases. There the key relation is
`q₀ − q₁ = q₂ − q₃`, with new points at `q₀` (first of the first pair) and
`q₃` (second of the second pair). Two Cauchy–Schwarz rounds
(`one_new_each_energy`) give the same bound. With the four witnesses
`(a, b, c, d)` of a failing triple, cases (b,d) and (a,c) regroup to
`lemma19_two_new_piece`, and cases (a,d) and (b,c) to `lemma19_mixed_piece`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- **[49] Lemma 19 in `ℤ/N`, two new points.** -/
theorem lemma19_two_new_piece {N : Nat} [NeZero N] [Fact N.Prime]
    (U W : ZMod N → Finset (ZMod N)) (hne : ∀ x, (U x).Nonempty)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    (T : Finset (Fin 4 → ZMod N)) (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (hadd : ∀ q ∈ T, q 0 - q 2 = q 1 - q 3 ∧ val q 0 - val q 2 = val q 1 - val q 3)
    (hU : ∀ q ∈ T, ∀ i, val q i ∈ U (q i))
    (hW : ∀ q ∈ T, val q 1 ∈ W (q 1) ∧ val q 3 ∈ W (q 3))
    (hcons : ∀ q ∈ T, ∀ i j, q i = q j → val q i = val q j)
    {δ : Real} (hδ : 0 < δ) (hT : δ * (N : Real) ^ 3 * (256 * K ^ 4) ≤ T.card) :
    ∃ f : ZMod N → ZMod N, (∀ x, f x ∈ U x) ∧
      ∃ E' : Finset (ZMod N), (∀ x ∈ E', f x ∈ W x) ∧
        (2 : Real) ^ (-(1882 : Real)) * (δ ^ 2) ^ 1164 * N ≤ E'.card ∧
        IsFreimanLinearOn E' f := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let rq := quadRequirement val
  let T' := T.image rq
  have hT' : ∀ r ∈ T', r.1.card ≤ 4 ∧ ∀ x ∈ r.1, r.2 x ∈ U x := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨?_, fun x hx => ?_⟩
    · calc (Finset.univ.image q).card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
        _ = 4 := by simp
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      show (quadRequirement val q).2 (q i) ∈ U (q i)
      rw [quadRequirement_value (hcons q hq) i]
      exact hU q hq i
  have hfiber : T.card ≤ 256 * T'.card := by
    apply Finset.card_le_mul_card_image
    intro r hr
    obtain ⟨q₀, _, rfl⟩ := Finset.mem_image.mp hr
    calc (T.filter fun q => rq q = rq q₀).card
        ≤ (Fintype.piFinset fun _ : Fin 4 => (rq q₀).1).card := by
          apply Finset.card_le_card
          intro q hq
          obtain ⟨_, hqr⟩ := Finset.mem_filter.mp hq
          rw [Fintype.mem_piFinset]
          intro i
          have : q i ∈ (rq q).1 := Finset.mem_image_of_mem q (Finset.mem_univ i)
          rwa [hqr] at this
      _ ≤ 256 := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have h4 : (rq q₀).1.card ≤ 4 := by
            calc (Finset.univ.image q₀).card ≤ (Finset.univ : Finset (Fin 4)).card :=
                  Finset.card_image_le
              _ = 4 := by simp
          calc (rq q₀).1.card ^ 4 ≤ 4 ^ 4 := Nat.pow_le_pow_left h4 4
            _ = 256 := by norm_num
  obtain ⟨f, hf, hmet⟩ := exists_good_selection U hne hK1 hK T' hT'
  refine ⟨f, fun x => Fintype.mem_piFinset.mp hf x, ?_⟩
  let A' := Finset.univ.filter fun x => f x ∈ W x
  -- met requirements give matched pairs-of-pairs
  have hcount : (T'.filter fun r => Meets f r).card ≤
      pairEnergy Finset.univ (A' ×ˢ A') f := by
    have hpre : ∀ r ∈ T'.filter (fun r => Meets f r), ∃ q ∈ T, rq q = r :=
      fun r hr => Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    choose g hgT hgr using hpre
    have hfq : ∀ r (hr : r ∈ T'.filter (fun r => Meets f r)) i,
        f (g r hr i) = val (g r hr) i := by
      intro r hr i
      have hmeets : Meets f (rq (g r hr)) := by
        rw [hgr r hr]
        exact (Finset.mem_filter.mp hr).2
      rw [hmeets (g r hr i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
      exact quadRequirement_value (hcons _ (hgT r hr)) i
    unfold pairEnergy
    calc (T'.filter fun r => Meets f r).card
        = ((T'.filter fun r => Meets f r).attach.image
            fun r => (((g r.1 r.2) 0, (g r.1 r.2) 2), ((g r.1 r.2) 1, (g r.1 r.2) 3))).card := by
          rw [Finset.card_image_of_injective, Finset.card_attach]
          intro r s hrs
          simp only [Prod.mk.injEq] at hrs
          obtain ⟨⟨h0, h2⟩, h1, h3⟩ := hrs
          have hq : g r.1 r.2 = g s.1 s.2 := by
            funext i
            fin_cases i
            · exact h0
            · exact h1
            · exact h2
            · exact h3
          have := congrArg rq hq
          rw [hgr, hgr] at this
          exact Subtype.ext this
      _ ≤ ((Finset.univ ×ˢ (A' ×ˢ A')).filter fun uv => pairKey f uv.1 = pairKey f uv.2).card := by
          apply Finset.card_le_card
          intro uv huv
          obtain ⟨⟨r, hr⟩, _, rfl⟩ := Finset.mem_image.mp huv
          have hq := hgT r hr
          obtain ⟨hd, hv⟩ := hadd _ hq
          obtain ⟨hw1, hw3⟩ := hW _ hq
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
            Finset.mem_product.mpr ⟨?_, ?_⟩⟩, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfq r hr 1]; exact hw1⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfq r hr 3]; exact hw3⟩
          · simp only [pairKey, Prod.mk.injEq]
            refine ⟨hd, ?_⟩
            rw [hfq r hr 0, hfq r hr 1, hfq r hr 2, hfq r hr 3]
            exact hv
  -- `X ≥ δN³`
  have hX : δ * (N : Real) ^ 3 ≤ pairEnergy Finset.univ (A' ×ˢ A') f := by
    have hK4 : (0 : Real) < 256 * K ^ 4 := by
      have : (1 : Real) ≤ K := by exact_mod_cast hK1
      positivity
    have h2 : T.card ≤ 256 * (K ^ 4 * (T'.filter fun r => Meets f r).card) :=
      hfiber.trans (Nat.mul_le_mul_left 256 hmet)
    have h1 : (T.card : Real) ≤ 256 * K ^ 4 * pairEnergy Finset.univ (A' ×ˢ A') f := by
      have h3 : T.card ≤ 256 * (K ^ 4 * pairEnergy Finset.univ (A' ×ˢ A') f) :=
        h2.trans (Nat.mul_le_mul_left 256 (Nat.mul_le_mul_left _ hcount))
      calc (T.card : Real) ≤ ((256 * (K ^ 4 * pairEnergy Finset.univ (A' ×ˢ A') f) : Nat) : Real) := by
            exact_mod_cast h3
        _ = 256 * K ^ 4 * pairEnergy Finset.univ (A' ×ˢ A') f := by push_cast; ring
    have h4 : δ * (N : Real) ^ 3 * (256 * K ^ 4) ≤
        pairEnergy Finset.univ (A' ×ˢ A') f * (256 * K ^ 4) := by
      calc _ ≤ (T.card : Real) := hT
        _ ≤ _ := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_right h4 hK4
  -- Cauchy–Schwarz: `δ²N³ ≤` respected quadruples in `A'`
  have henergy : δ ^ 2 * (N : Real) ^ 3 ≤
      weightedSimultaneousAdditiveEnergy A' (fun _ => 1) (fun _ : Fin 1 => f) := by
    rw [energy_eq_phiAdditiveCount]
    have hcs := two_new_points_energy A' f
    have hcsR : ((pairEnergy Finset.univ (A' ×ˢ A') f : Nat) : Real) ^ 2 ≤
        (N : Real) ^ 3 * phiAdditiveCount A' f := by exact_mod_cast hcs
    have hsq : (δ * (N : Real) ^ 3) ^ 2 ≤ ((pairEnergy Finset.univ (A' ×ˢ A') f : Nat) : Real) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hX 2
    have hN3 : (0 : Real) < (N : Real) ^ 3 := by positivity
    have : δ ^ 2 * (N : Real) ^ 3 * (N : Real) ^ 3 ≤ (N : Real) ^ 3 * phiAdditiveCount A' f := by
      calc δ ^ 2 * (N : Real) ^ 3 * (N : Real) ^ 3 = (δ * (N : Real) ^ 3) ^ 2 := by ring
        _ ≤ _ := hsq
        _ ≤ _ := hcsR
    rw [mul_comm ((N : Real) ^ 3)] at this
    exact le_of_mul_le_mul_right this hN3
  obtain ⟨E', hE'A, hE'card, hE'F⟩ :=
    lineFreimanExtraction_holds.2 N A' f (δ ^ 2) (by positivity) henergy
  exact ⟨E', fun x hx => (Finset.mem_filter.mp (hE'A hx)).2, hE'card, hE'F⟩

/-- **[49] Lemma 19 in `ℤ/N`, mixed case: one new point in each pair.** -/
theorem lemma19_mixed_piece {N : Nat} [NeZero N] [Fact N.Prime]
    (U W : ZMod N → Finset (ZMod N)) (hne : ∀ x, (U x).Nonempty)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    (T : Finset (Fin 4 → ZMod N)) (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (hadd : ∀ q ∈ T, q 0 - q 1 = q 2 - q 3 ∧ val q 0 - val q 1 = val q 2 - val q 3)
    (hU : ∀ q ∈ T, ∀ i, val q i ∈ U (q i))
    (hW : ∀ q ∈ T, val q 0 ∈ W (q 0) ∧ val q 3 ∈ W (q 3))
    (hcons : ∀ q ∈ T, ∀ i j, q i = q j → val q i = val q j)
    {δ : Real} (hδ : 0 < δ) (hT : δ * (N : Real) ^ 3 * (256 * K ^ 4) ≤ T.card) :
    ∃ f : ZMod N → ZMod N, (∀ x, f x ∈ U x) ∧
      ∃ E' : Finset (ZMod N), (∀ x ∈ E', f x ∈ W x) ∧
        (2 : Real) ^ (-(1882 : Real)) * (δ ^ 2) ^ 1164 * N ≤ E'.card ∧
        IsFreimanLinearOn E' f := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let rq := quadRequirement val
  let T' := T.image rq
  have hT' : ∀ r ∈ T', r.1.card ≤ 4 ∧ ∀ x ∈ r.1, r.2 x ∈ U x := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨?_, fun x hx => ?_⟩
    · calc (Finset.univ.image q).card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
        _ = 4 := by simp
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      show (quadRequirement val q).2 (q i) ∈ U (q i)
      rw [quadRequirement_value (hcons q hq) i]
      exact hU q hq i
  have hfiber : T.card ≤ 256 * T'.card := by
    apply Finset.card_le_mul_card_image
    intro r hr
    obtain ⟨q₀, _, rfl⟩ := Finset.mem_image.mp hr
    calc (T.filter fun q => rq q = rq q₀).card
        ≤ (Fintype.piFinset fun _ : Fin 4 => (rq q₀).1).card := by
          apply Finset.card_le_card
          intro q hq
          obtain ⟨_, hqr⟩ := Finset.mem_filter.mp hq
          rw [Fintype.mem_piFinset]
          intro i
          have : q i ∈ (rq q).1 := Finset.mem_image_of_mem q (Finset.mem_univ i)
          rwa [hqr] at this
      _ ≤ 256 := by
          rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          have h4 : (rq q₀).1.card ≤ 4 := by
            calc (Finset.univ.image q₀).card ≤ (Finset.univ : Finset (Fin 4)).card :=
                  Finset.card_image_le
              _ = 4 := by simp
          calc (rq q₀).1.card ^ 4 ≤ 4 ^ 4 := Nat.pow_le_pow_left h4 4
            _ = 256 := by norm_num
  obtain ⟨f, hf, hmet⟩ := exists_good_selection U hne hK1 hK T' hT'
  refine ⟨f, fun x => Fintype.mem_piFinset.mp hf x, ?_⟩
  let A' := Finset.univ.filter fun x => f x ∈ W x
  -- met requirements give matched pairs-of-pairs
  let S₁ := Finset.univ.filter fun p : ZMod N × ZMod N => p.1 ∈ A'
  let S₂ := Finset.univ.filter fun p : ZMod N × ZMod N => p.2 ∈ A'
  have hcount : (T'.filter fun r => Meets f r).card ≤ pairEnergy S₁ S₂ f := by
    have hpre : ∀ r ∈ T'.filter (fun r => Meets f r), ∃ q ∈ T, rq q = r :=
      fun r hr => Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    choose g hgT hgr using hpre
    have hfq : ∀ r (hr : r ∈ T'.filter (fun r => Meets f r)) i,
        f (g r hr i) = val (g r hr) i := by
      intro r hr i
      have hmeets : Meets f (rq (g r hr)) := by
        rw [hgr r hr]
        exact (Finset.mem_filter.mp hr).2
      rw [hmeets (g r hr i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))]
      exact quadRequirement_value (hcons _ (hgT r hr)) i
    unfold pairEnergy
    calc (T'.filter fun r => Meets f r).card
        = ((T'.filter fun r => Meets f r).attach.image
            fun r => (((g r.1 r.2) 0, (g r.1 r.2) 1), ((g r.1 r.2) 2, (g r.1 r.2) 3))).card := by
          rw [Finset.card_image_of_injective, Finset.card_attach]
          intro r s hrs
          simp only [Prod.mk.injEq] at hrs
          obtain ⟨⟨h0, h1⟩, h2, h3⟩ := hrs
          have hq : g r.1 r.2 = g s.1 s.2 := by
            funext i
            fin_cases i
            · exact h0
            · exact h1
            · exact h2
            · exact h3
          have := congrArg rq hq
          rw [hgr, hgr] at this
          exact Subtype.ext this
      _ ≤ ((S₁ ×ˢ S₂).filter fun uv => pairKey f uv.1 = pairKey f uv.2).card := by
          apply Finset.card_le_card
          intro uv huv
          obtain ⟨⟨r, hr⟩, _, rfl⟩ := Finset.mem_image.mp huv
          have hq := hgT r hr
          obtain ⟨hd, hv⟩ := hadd _ hq
          obtain ⟨hw0, hw3⟩ := hW _ hq
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, by rw [hfq r hr 0]; exact hw0⟩⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, by rw [hfq r hr 3]; exact hw3⟩⟩
          · simp only [pairKey, Prod.mk.injEq]
            refine ⟨hd, ?_⟩
            rw [hfq r hr 0, hfq r hr 1, hfq r hr 2, hfq r hr 3]
            exact hv
  -- `X ≥ δN³`
  have hX : δ * (N : Real) ^ 3 ≤ pairEnergy S₁ S₂ f := by
    have hK4 : (0 : Real) < 256 * K ^ 4 := by
      have : (1 : Real) ≤ K := by exact_mod_cast hK1
      positivity
    have h2 : T.card ≤ 256 * (K ^ 4 * (T'.filter fun r => Meets f r).card) :=
      hfiber.trans (Nat.mul_le_mul_left 256 hmet)
    have h1 : (T.card : Real) ≤ 256 * K ^ 4 * pairEnergy S₁ S₂ f := by
      have h3 : T.card ≤ 256 * (K ^ 4 * pairEnergy S₁ S₂ f) :=
        h2.trans (Nat.mul_le_mul_left 256 (Nat.mul_le_mul_left _ hcount))
      calc (T.card : Real) ≤ ((256 * (K ^ 4 * pairEnergy S₁ S₂ f) : Nat) : Real) := by
            exact_mod_cast h3
        _ = 256 * K ^ 4 * pairEnergy S₁ S₂ f := by push_cast; ring
    have h4 : δ * (N : Real) ^ 3 * (256 * K ^ 4) ≤
        pairEnergy S₁ S₂ f * (256 * K ^ 4) := by
      calc _ ≤ (T.card : Real) := hT
        _ ≤ _ := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_right h4 hK4
  -- Cauchy–Schwarz: `δ²N³ ≤` respected quadruples in `A'`
  have henergy : δ ^ 2 * (N : Real) ^ 3 ≤
      weightedSimultaneousAdditiveEnergy A' (fun _ => 1) (fun _ : Fin 1 => f) := by
    rw [energy_eq_phiAdditiveCount]
    have hcs := one_new_each_energy A' f
    have hcsR : ((pairEnergy S₁ S₂ f : Nat) : Real) ^ 2 ≤
        (N : Real) ^ 3 * phiAdditiveCount A' f := by exact_mod_cast hcs
    have hsq : (δ * (N : Real) ^ 3) ^ 2 ≤ ((pairEnergy S₁ S₂ f : Nat) : Real) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hX 2
    have hN3 : (0 : Real) < (N : Real) ^ 3 := by positivity
    have : δ ^ 2 * (N : Real) ^ 3 * (N : Real) ^ 3 ≤ (N : Real) ^ 3 * phiAdditiveCount A' f := by
      calc δ ^ 2 * (N : Real) ^ 3 * (N : Real) ^ 3 = (δ * (N : Real) ^ 3) ^ 2 := by ring
        _ ≤ _ := hsq
        _ ≤ _ := hcsR
    rw [mul_comm ((N : Real) ^ 3)] at this
    exact le_of_mul_le_mul_right this hN3
  obtain ⟨E', hE'A, hE'card, hE'F⟩ :=
    lineFreimanExtraction_holds.2 N A' f (δ ^ 2) (by positivity) henergy
  exact ⟨E', fun x hx => (Finset.mem_filter.mp (hE'A hx)).2, hE'card, hE'F⟩

end LeanProofs.GowersSzemeredi
