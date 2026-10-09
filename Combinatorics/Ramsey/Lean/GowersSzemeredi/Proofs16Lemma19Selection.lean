import GowersSzemeredi.Proofs16SelectionAveraging

/-! [49] Lemma 19 in `ℤ/N`, with polynomial bounds.

arXiv:2109.03093, Lemma 19. Prescribed values `val q` on many additive
quadruples `q` are realised simultaneously by one selection `f(y) ∈ U_y`.
That selection is then Freiman-linear on a large set where it takes "new"
values, `f(y) ∈ W_y`. [49] uses a random selection and Theorem 17 (Sanders).
Here:
* a quadruple becomes a requirement on its image set (`quadRequirement`);
  each requirement has at most `4⁴ = 256` preimages;
* `exists_good_selection` (deterministic averaging) gives `f` meeting
  `≥ |T|/(256K⁴)` of the quadruples, each of which `f` then respects inside
  `A′ = {y : f y ∈ W y}`;
* `lineFreimanExtraction_holds` (Gowers's Corollary 7.6) turns that energy
  into a Freiman-linear piece of size `≥ κ(δ)N`, with
  `κ(δ) = 2^(−1882)δ^1164`.

`lemma19_selection_piece`: if `δN³·256K⁴ ≤ |T|`, there is a selection `f`
and `E′` with `f(y) ∈ W_y` on `E′`, `|E′| ≥ κ(δ)N`, and `f` Freiman-linear on
`E′`. Lemma 7.8 then extends such a piece to a Bohr set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The requirement imposed by a valued quadruple. -/
def quadRequirement {N : Nat} [NeZero N] (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (q : Fin 4 → ZMod N) : Finset (ZMod N) × (ZMod N → ZMod N) :=
  (Finset.univ.image q, fun x => if h : ∃ i, q i = x then val q h.choose else 0)

theorem quadRequirement_value {N : Nat} [NeZero N] {val : (Fin 4 → ZMod N) → Fin 4 → ZMod N}
    {q : Fin 4 → ZMod N} (hcons : ∀ i j, q i = q j → val q i = val q j) (i : Fin 4) :
    (quadRequirement val q).2 (q i) = val q i := by
  have h : ∃ j, q j = q i := ⟨i, rfl⟩
  simp only [quadRequirement, dif_pos h]
  exact hcons _ _ h.choose_spec

/-- **[49] Lemma 19 in `ℤ/N`.** -/
theorem lemma19_selection_piece {N : Nat} [NeZero N] [Fact N.Prime]
    (U W : ZMod N → Finset (ZMod N)) (hWU : ∀ x, W x ⊆ U x) (hne : ∀ x, (U x).Nonempty)
    {K : Nat} (hK1 : 1 ≤ K) (hK : ∀ x, (U x).card ≤ K)
    (T : Finset (Fin 4 → ZMod N)) (val : (Fin 4 → ZMod N) → Fin 4 → ZMod N)
    (hadd : ∀ q ∈ T, q 0 + q 1 = q 2 + q 3 ∧ val q 0 + val q 1 = val q 2 + val q 3)
    (hW : ∀ q ∈ T, ∀ i, val q i ∈ W (q i))
    (hcons : ∀ q ∈ T, ∀ i j, q i = q j → val q i = val q j)
    {δ : Real} (hδ : 0 < δ) (hT : δ * (N : Real) ^ 3 * (256 * K ^ 4) ≤ T.card) :
    ∃ f : ZMod N → ZMod N, (∀ x, f x ∈ U x) ∧
      ∃ E' : Finset (ZMod N), (∀ x ∈ E', f x ∈ W x) ∧
        (2 : Real) ^ (-(1882 : Real)) * δ ^ 1164 * N ≤ E'.card ∧ IsFreimanLinearOn E' f := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let rq := quadRequirement val
  let T' := T.image rq
  -- requirements are admissible
  have hT' : ∀ r ∈ T', r.1.card ≤ 4 ∧ ∀ x ∈ r.1, r.2 x ∈ U x := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨?_, fun x hx => ?_⟩
    · calc (Finset.univ.image q).card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
        _ = 4 := by simp
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      show (quadRequirement val q).2 (q i) ∈ U (q i)
      rw [quadRequirement_value (hcons q hq) i]
      exact hWU _ (hW q hq i)
  -- each requirement has at most `256` preimages
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
  -- the set of new values and the respected quadruples
  let A' := Finset.univ.filter fun x => f x ∈ W x
  have hcount : (T'.filter fun r => Meets f r).card ≤ phiAdditiveCount A' f := by
    -- each met requirement has a preimage quadruple, respected by `f` inside `A'`
    have hpre : ∀ r ∈ T'.filter (fun r => Meets f r), ∃ q ∈ T, rq q = r :=
      fun r hr => Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    choose g hgT hgr using hpre
    unfold phiAdditiveCount countWhere
    calc (T'.filter fun r => Meets f r).card
        = ((T'.filter fun r => Meets f r).attach.image fun r => g r.1 r.2).card := by
          rw [Finset.card_image_of_injective, Finset.card_attach]
          intro r s hrs
          have := congrArg rq hrs
          simp only [hgr] at this
          exact Subtype.ext this
      _ ≤ (Finset.univ.filter (IsPhiAdditive A' f)).card := by
          apply Finset.card_le_card
          intro q hq
          obtain ⟨⟨r, hr⟩, _, rfl⟩ := Finset.mem_image.mp hq
          have hqT := hgT r hr
          have hmeets : Meets f (rq (g r hr)) := by
            rw [hgr r hr]
            exact (Finset.mem_filter.mp hr).2
          have hfq : ∀ i, f (g r hr i) = val (g r hr) i := by
            intro i
            have := hmeets (g r hr i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
            rw [this]
            exact quadRequirement_value (hcons _ hqT) i
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_, (hadd _ hqT).1, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hfq i]; exact hW _ hqT i⟩
          · rw [hfq 0, hfq 1, hfq 2, hfq 3]
            exact (hadd _ hqT).2
  -- the energy bound
  have henergy : δ * (N : Real) ^ 3 ≤
      weightedSimultaneousAdditiveEnergy A' (fun _ => 1) (fun _ : Fin 1 => f) := by
    rw [energy_eq_phiAdditiveCount]
    have hK4 : (0 : Real) < 256 * K ^ 4 := by
      have : (1 : Real) ≤ K := by exact_mod_cast hK1
      positivity
    have h1 : (T.card : Real) ≤ 256 * K ^ 4 * (T'.filter fun r => Meets f r).card := by
      have h2 : T.card ≤ 256 * (K ^ 4 * (T'.filter fun r => Meets f r).card) :=
        hfiber.trans (Nat.mul_le_mul_left 256 hmet)
      calc (T.card : Real) ≤ ((256 * (K ^ 4 * (T'.filter fun r => Meets f r).card) : Nat) : Real) := by
            exact_mod_cast h2
        _ = 256 * K ^ 4 * (T'.filter fun r => Meets f r).card := by push_cast; ring
    have h3 : ((T'.filter fun r => Meets f r).card : Real) ≤ phiAdditiveCount A' f := by
      exact_mod_cast hcount
    have h4 : δ * (N : Real) ^ 3 * (256 * K ^ 4) ≤ phiAdditiveCount A' f * (256 * K ^ 4) := by
      calc δ * (N : Real) ^ 3 * (256 * K ^ 4) ≤ T.card := hT
        _ ≤ 256 * K ^ 4 * (T'.filter fun r => Meets f r).card := h1
        _ ≤ 256 * K ^ 4 * phiAdditiveCount A' f := mul_le_mul_of_nonneg_left h3 hK4.le
        _ = phiAdditiveCount A' f * (256 * K ^ 4) := by ring
    exact le_of_mul_le_mul_right h4 hK4
  obtain ⟨E', hE'A, hE'card, hE'F⟩ := lineFreimanExtraction_holds.2 N A' f δ hδ henergy
  exact ⟨E', fun x hx => (Finset.mem_filter.mp (hE'A hx)).2, hE'card, hE'F⟩

end LeanProofs.GowersSzemeredi
