import GowersSzemeredi.Proofs16PropNineThreeIteration
import GowersSzemeredi.Proofs16ClaimNineFive

/-! The 12-tuple rounds and the full iteration of Milićević's
Proposition 9.3 (arXiv:2601.01682, printed p. 67): "apply repeatedly
Claims 9.4 and 9.5 until a `1 − ε` proportion of additive quadruples satisfy
(24) and a `1 − ε` proportion of the 12-tuples satisfy (26)".

**Bad 12-tuples** (`propNineThreeBad12`). Write `K_u = ⋃_j (Γ_{x_j+a_j} ∪
Γ_{x_j})` and `L_u = ⋃_j (Γ_{y_j+a_j} ∪ Γ_{y_j})`. A 12-tuple is bad when some
`d` is small against all current `θ_i(a_j)` but `d ∉ B(K_u; ρ) + B(L_u; ρ)`.
Since `B(K_u; ρ) = ⋂_j B_{x_j+a_j} ∩ B_{x_j} ⊆ ∑_j (B_{x_j+a_j} ∩ B_{x_j})`,
a good 12-tuple satisfies Milićević's (26).

**One Claim 9.5 round** (`milicevic_prop_9_3_round_twelve`).
1. Theorem 27 at rank `8d` gives `ξ ∈ ⟨K_u⟩_R ∩ ⟨L_u⟩_R`, outside the
   radius-4 bounded span of all current values.
2. `spanBall_biUnion_split` and `spanBall_union_split` cut `ξ` into
   sixteen span-ball pieces.
3. If every `ξ_{j,0} − ξ_{j,1}` lay in `⟨θ_i(a_j) : i ∈ I_{x_j,a_j}⟩_1`, their
   sum would lie in the radius-4 span (`sum_mem_spanBall_of_subset`).
   So some coordinate escapes, and `claim_9_5` applies.

**Termination** (`milicevic_prop_9_3_iteration`). With
`δ = min(claimNineFourDensity, claimNineFiveDensity)`, each round raises
`∑|I_{x,a}| ≤ N²s₀` by `⌈δN²⌉`. The iteration reaches a state with fewer
than `εN³` bad triples and fewer than `εN¹¹` bad 12-tuples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem spanBall_empty_eq {G : Type*} [AddCommGroup G] {R : Nat} {ξ : G}
    (h : ξ ∈ spanBall (∅ : Finset G) R) : ξ = 0 := by
  obtain ⟨n, -, rfl⟩ := (mem_spanBall_iff _ R ξ).mp h
  simp

/-- **Splitting over a finite union.** -/
theorem spanBall_biUnion_split {G ι : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq ι]
    (s : Finset ι) (f : ι → Finset G) (R : Nat) {ξ : G} (h : ξ ∈ spanBall (s.biUnion f) R) :
    ∃ α : ι → G, (∀ i ∈ s, α i ∈ spanBall (f i) R) ∧ ξ = ∑ i ∈ s, α i := by
  induction s using Finset.induction_on generalizing ξ with
  | empty =>
    rw [Finset.biUnion_empty] at h
    exact ⟨fun _ => 0, fun i hi => absurd hi (Finset.notMem_empty i), by
      rw [spanBall_empty_eq h, Finset.sum_empty]⟩
  | insert a s ha ih =>
    rw [Finset.biUnion_insert] at h
    obtain ⟨β, hβ, γ, hγ, rfl⟩ := spanBall_union_split _ _ R h
    obtain ⟨α', hα', hsum⟩ := ih hγ
    refine ⟨fun i => if i = a then β else α' i, fun i hi => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · simp only [if_pos rfl]; exact hβ
      · have hia : i ≠ a := fun e => ha (e ▸ hi)
        simp only [if_neg hia]; exact hα' i hi
    · rw [Finset.sum_insert ha, if_pos rfl, hsum]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by
        rw [if_neg (show i ≠ a from fun e => ha (e ▸ hi))]

/-- Span balls of subsets add into the span ball of the whole set. -/
theorem add_mem_spanBall_of_subset {G : Type*} [AddCommGroup G] {Γ Γ₁ Γ₂ : Finset G}
    {R₁ R₂ : Nat} {α β : G} (h₁ : Γ₁ ⊆ Γ) (h₂ : Γ₂ ⊆ Γ)
    (hα : α ∈ spanBall Γ₁ R₁) (hβ : β ∈ spanBall Γ₂ R₂) :
    α + β ∈ spanBall Γ (R₁ + R₂) := by
  obtain ⟨n₁, hn₁, rfl⟩ := (mem_spanBall_iff _ R₁ _).mp hα
  obtain ⟨n₂, hn₂, rfl⟩ := (mem_spanBall_iff _ R₂ _).mp hβ
  refine (mem_spanBall_iff _ (R₁ + R₂) _).mpr
    ⟨fun γ => (if γ ∈ Γ₁ then n₁ γ else 0) + (if γ ∈ Γ₂ then n₂ γ else 0), ?_, ?_⟩
  · intro γ _
    show -((R₁ + R₂ : Nat) : Int) ≤ (if γ ∈ Γ₁ then n₁ γ else 0) + (if γ ∈ Γ₂ then n₂ γ else 0) ∧
      (if γ ∈ Γ₁ then n₁ γ else 0) + (if γ ∈ Γ₂ then n₂ γ else 0) ≤ ((R₁ + R₂ : Nat) : Int)
    have e1 : -(R₁ : Int) ≤ (if γ ∈ Γ₁ then n₁ γ else 0) ∧ (if γ ∈ Γ₁ then n₁ γ else 0) ≤ R₁ := by
      split_ifs with h
      · exact hn₁ γ h
      · constructor <;> omega
    have e2 : -(R₂ : Int) ≤ (if γ ∈ Γ₂ then n₂ γ else 0) ∧ (if γ ∈ Γ₂ then n₂ γ else 0) ≤ R₂ := by
      split_ifs with h
      · exact hn₂ γ h
      · constructor <;> omega
    push_cast
    constructor <;> omega
  · have e : ∀ (Γ' : Finset G) (n : G → Int), Γ' ⊆ Γ →
        ∑ γ ∈ Γ, (if γ ∈ Γ' then n γ else 0) • γ = ∑ γ ∈ Γ', n γ • γ := by
      intro Γ' n hsub
      simp_rw [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    rw [← e Γ₁ n₁ h₁, ← e Γ₂ n₂ h₂, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [add_smul]

/-- A sum of radius-one span-ball elements of subsets of `W`. -/
theorem sum_mem_spanBall_of_subset {G ι : Type*} [AddCommGroup G] {W : Finset G}
    (s : Finset ι) (V : ι → Finset G) (α : ι → G) (hV : ∀ i ∈ s, V i ⊆ W)
    (hα : ∀ i ∈ s, α i ∈ spanBall (V i) 1) : ∑ i ∈ s, α i ∈ spanBall W s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_spanBall W 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, add_comm s.card 1]
    exact add_mem_spanBall_of_subset (hV a (Finset.mem_insert_self _ _)) le_rfl
      (hα a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hV i (Finset.mem_insert_of_mem hi))
        (fun i hi => hα i (Finset.mem_insert_of_mem hi)))

/-- `K_u = ⋃_j (Γ_{x_j+a_j} ∪ Γ_{x_j})`. -/
def twelveK {N : Nat} (Γ : ZMod N → Finset (ZMod N)) (u : Fin 11 → ZMod N) :
    Finset (ZMod N) :=
  Finset.univ.biUnion fun j : Fin 4 => Γ (twelvePoint u j 0) ∪ Γ (twelvePoint u j 1)

/-- `L_u = ⋃_j (Γ_{y_j+a_j} ∪ Γ_{y_j})`. -/
def twelveL {N : Nat} (Γ : ZMod N → Finset (ZMod N)) (u : Fin 11 → ZMod N) :
    Finset (ZMod N) :=
  Finset.univ.biUnion fun j : Fin 4 => Γ (twelvePoint u j 2) ∪ Γ (twelvePoint u j 3)

/-- The 12-tuples on which containment (26) fails. -/
def propNineThreeBad12 {N : Nat} [NeZero N] (Γ : ZMod N → Finset (ZMod N)) (rho η : Real)
    (θ : Nat → ZMod N → ZMod N) (I : ZMod N → ZMod N → Finset Nat) :
    Finset (Fin 11 → ZMod N) :=
  Finset.univ.filter fun u => ∃ d : ZMod N,
    (∀ j, ∀ i ∈ I (twelveX u j) (twelveA u j) ∪ I (twelveY u j) (twelveA u j),
      (centeredAbs (θ i (twelveA u j) * d) : Real) ≤ η * N) ∧
    ¬ ∃ v ∈ bohr (twelveK Γ u) rho, ∃ w ∈ bohr (twelveL Γ u) rho, d = v + w

theorem twelveK_card_le {N : Nat} (Γ : ZMod N → Finset (ZMod N)) {d : Nat}
    (hΓ : ∀ z, (Γ z).card ≤ d) (u : Fin 11 → ZMod N) : (twelveK Γ u).card ≤ 8 * d := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ j : Fin 4, (Γ (twelvePoint u j 0) ∪ Γ (twelvePoint u j 1)).card
      ≤ ∑ _j : Fin 4, 2 * d := Finset.sum_le_sum fun j _ =>
        (Finset.card_union_le _ _).trans (by
          have := hΓ (twelvePoint u j 0); have := hΓ (twelvePoint u j 1); omega)
    _ = 8 * d := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

theorem twelveL_card_le {N : Nat} (Γ : ZMod N → Finset (ZMod N)) {d : Nat}
    (hΓ : ∀ z, (Γ z).card ≤ d) (u : Fin 11 → ZMod N) : (twelveL Γ u).card ≤ 8 * d := by
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ j : Fin 4, (Γ (twelvePoint u j 2) ∪ Γ (twelvePoint u j 3)).card
      ≤ ∑ _j : Fin 4, 2 * d := Finset.sum_le_sum fun j _ =>
        (Finset.card_union_le _ _).trans (by
          have := hΓ (twelvePoint u j 2); have := hΓ (twelvePoint u j 3); omega)
    _ = 8 * d := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

/-- **One Claim 9.5 round of Proposition 9.3.** -/
theorem milicevic_prop_9_3_round_twelve {N : Nat} [NeZero N] [Fact N.Prime]
    (Γ : ZMod N → Finset (ZMod N)) {d : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) {r : Nat}
    (hr : 8 * d ≤ r) (M : Nat) [NeZero M] {rho : Real} (hrho : 0 < rho) (hrho1 : rho < 1)
    (hM : 2 ≤ rho * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius r M rho) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 32 * (s₀ : Real) * η ≤ 1 / 4) {ε : Real} (hε : 0 < ε)
    {m : Nat} {θ : Nat → ZMod N → ZMod N} {D : Nat → Finset (ZMod N)}
    {I : ZMod N → ZMod N → Finset Nat}
    (hinv : PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) m θ D I)
    (hbad : ε * (N : Real) ^ 11 ≤ (propNineThreeBad12 Γ rho η θ I).card) :
    ∃ (θ' : Nat → ZMod N → ZMod N) (D' : Nat → Finset (ZMod N))
      (I' : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) (m + 1) θ' D' I' ∧
      (propNineThreePotential I : Real) +
          claimNineFiveDensity ε (propNineThreeRadius r M rho) d * (N : Real) ^ 2 ≤
        propNineThreePotential I' := by
  set R := propNineThreeRadius r M rho with hRdef
  set Bad := propNineThreeBad12 Γ rho η θ I with hBad
  have hcap := propNineThree_index_card_le Γ hΓ hs₀ hinv
  let V : (Fin 11 → ZMod N) → Fin 4 → Finset (ZMod N) := fun u j =>
    (I (twelveX u j) (twelveA u j)).image fun i => θ i (twelveA u j)
  have key : ∀ u : Fin 11 → ZMod N, ∃ ξ : Fin 4 → Fin 4 → ZMod N, u ∈ Bad →
      (∀ j k, ξ j k ∈ spanBall (Γ (twelvePoint u j k)) R) ∧
      ∑ j, (ξ j 0 - ξ j 1) = ∑ j, (ξ j 2 - ξ j 3) ∧
      ∃ j, ξ j 0 - ξ j 1 ∉ spanBall (V u j) 1 := by
    intro u
    by_cases hu : u ∈ Bad
    · obtain ⟨-, dd, hdd, hnot⟩ := Finset.mem_filter.mp hu
      set W := Finset.univ.biUnion fun j : Fin 4 =>
        (I (twelveX u j) (twelveA u j) ∪ I (twelveY u j) (twelveA u j)).image
          fun i => θ i (twelveA u j) with hW
      have hWcard : (Fintype.card W : Real) * ((4 : Nat) : Real) * η ≤ 1 / 4 := by
        rw [Fintype.card_coe]
        have h1 : W.card ≤ 8 * s₀ := by
          refine Finset.card_biUnion_le.trans ?_
          calc ∑ j : Fin 4, ((I (twelveX u j) (twelveA u j) ∪
                I (twelveY u j) (twelveA u j)).image fun i => θ i (twelveA u j)).card
              ≤ ∑ _j : Fin 4, 2 * s₀ := Finset.sum_le_sum fun j _ =>
                Finset.card_image_le.trans ((Finset.card_union_le _ _).trans (by
                  have := hcap (twelveX u j) (twelveA u j)
                  have := hcap (twelveY u j) (twelveA u j)
                  omega))
            _ = 8 * s₀ := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        have h2 : (W.card : Real) ≤ 8 * s₀ := by exact_mod_cast h1
        push_cast
        nlinarith
      have hWd : ∀ w : W, (centeredAbs ((w : ZMod N) * dd) : Real) ≤ η * N := by
        intro w
        obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp w.2
        obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hj
        rw [← hiw]
        exact hdd j i hi
      obtain ⟨ξ, hξKL, hξesc⟩ := escape_frequency_uniform (twelveK Γ u) (twelveL Γ u) r M
        ((twelveK_card_le Γ hΓ u).trans hr) ((twelveL_card_le Γ hΓ u).trans hr)
        hrho hrho1 hM (fun w : W => (w : ZMod N)) 4 hWcard hWd hnot
      obtain ⟨hξK, hξL⟩ := Finset.mem_inter.mp hξKL
      obtain ⟨α, hα, hαsum⟩ := spanBall_biUnion_split _ _ R
        (boundedFrequencySpan_subset_spanBall _ R hξK)
      obtain ⟨α', hα', hα'sum⟩ := spanBall_biUnion_split _ _ R
        (boundedFrequencySpan_subset_spanBall _ R hξL)
      have hsplit : ∀ j, ∃ β₀ ∈ spanBall (Γ (twelvePoint u j 0)) R,
          ∃ β₁ ∈ spanBall (Γ (twelvePoint u j 1)) R, α j = β₀ + β₁ := fun j =>
        spanBall_union_split _ _ R (hα j (Finset.mem_univ _))
      have hsplit' : ∀ j, ∃ β₂ ∈ spanBall (Γ (twelvePoint u j 2)) R,
          ∃ β₃ ∈ spanBall (Γ (twelvePoint u j 3)) R, α' j = β₂ + β₃ := fun j =>
        spanBall_union_split _ _ R (hα' j (Finset.mem_univ _))
      choose β₀ hβ₀ β₁ hβ₁ hβ using hsplit
      choose β₂ hβ₂ β₃ hβ₃ hβ' using hsplit'
      refine ⟨fun j => ![β₀ j, -β₁ j, β₂ j, -β₃ j], fun _ => ⟨?_, ?_, ?_⟩⟩
      · intro j k
        fin_cases k
        · exact hβ₀ j
        · exact neg_mem_spanBall (hβ₁ j)
        · exact hβ₂ j
        · exact neg_mem_spanBall (hβ₃ j)
      · show ∑ j, (β₀ j - -β₁ j) = ∑ j, (β₂ j - -β₃ j)
        simp only [sub_neg_eq_add]
        rw [← Finset.sum_congr rfl fun j _ => hβ j, ← Finset.sum_congr rfl fun j _ => hβ' j,
          ← hαsum, ← hα'sum]
      · by_contra hall
        push Not at hall
        apply hξesc
        have hmem : ∑ j, α j ∈ spanBall W (Finset.univ : Finset (Fin 4)).card := by
          refine sum_mem_spanBall_of_subset Finset.univ (V u) α (fun j _ => ?_) (fun j _ => ?_)
          · intro w hw
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
            exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
              Finset.mem_image.mpr ⟨i, Finset.mem_union_left _ hi, rfl⟩⟩
          · have := hall j
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add] at this
            rw [hβ j]
            exact this
        rw [Finset.card_univ, Fintype.card_fin, ← hαsum] at hmem
        exact spanBall_subset_boundedFrequencySpan le_rfl 4 hmem
    · exact ⟨fun _ _ => 0, fun h => absurd h hu⟩
  choose ξ hξ using key
  obtain ⟨Θ, B, P, hF, hPcard, hP⟩ := claim_9_5 Γ hΓ Bad ξ (fun u hu => (hξ u hu).1)
    (fun u hu => (hξ u hu).2.1)
    (fun x a => spanBall ((I x a).image fun i => θ i a) 1) (fun u hu => (hξ u hu).2.2)
    hε hbad
  obtain ⟨θ', D', I', hinv', hpot⟩ := propNineThree_append hinv Θ B P hF hP
  refine ⟨θ', D', I', hinv', ?_⟩
  rw [hpot]
  push_cast
  linarith

/-- **The iteration of Proposition 9.3 terminates.** From the empty state,
Claim 9.4 and Claim 9.5 rounds reach a state with fewer than `εN³` bad triples
and fewer than `εN¹¹` bad 12-tuples, after `m` rounds with `⌈δN²⌉·m ≤ N²s₀`
and `δ = min(claimNineFourDensity, claimNineFiveDensity)`. -/
theorem milicevic_prop_9_3_iteration {N : Nat} [NeZero N] [Fact N.Prime]
    (Γ : ZMod N → Finset (ZMod N)) {d : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) {r : Nat}
    (hr : 8 * d ≤ r) (M : Nat) [NeZero M] {rho : Real} (hrho : 0 < rho) (hrho1 : rho < 1)
    (hM : 2 ≤ rho * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius r M rho) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 32 * (s₀ : Real) * η ≤ 1 / 4) {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (θ : Nat → ZMod N → ZMod N) (D : Nat → Finset (ZMod N))
      (I : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) m θ D I ∧
      ((propNineThreeBad Γ rho η θ I).card : Real) < ε * (N : Real) ^ 3 ∧
      ((propNineThreeBad12 Γ rho η θ I).card : Real) < ε * (N : Real) ^ 11 ∧
      ⌈min (claimNineFourDensity ε (propNineThreeRadius r M rho) d)
          (claimNineFiveDensity ε (propNineThreeRadius r M rho) d) * (N : Real) ^ 2⌉₊ * m ≤
        N * N * s₀ := by
  set R := propNineThreeRadius r M rho with hRdef
  set R' := 2 * R with hR'
  set δ := min (claimNineFourDensity ε R d) (claimNineFiveDensity ε R d) with hδ
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hKpos : (0 : Real) < (((2 * R + 1) ^ d : Nat) : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hδ4 : 0 < claimNineFourDensity ε R d := by
    simp only [claimNineFourDensity]
    positivity
  have hδ12 : 0 < claimNineFiveDensity ε R d := by
    simp only [claimNineFiveDensity]
    positivity
  have hδpos : 0 < δ := lt_min hδ4 hδ12
  have hη2 : 2 * (s₀ : Real) * η ≤ 1 / 4 := by
    have : (0 : Real) ≤ s₀ * η := mul_nonneg (Nat.cast_nonneg _) hη0
    nlinarith
  have hr2 : 2 * d ≤ r := by omega
  set k := ⌈δ * (N : Real) ^ 2⌉₊ with hk
  have hN2 : (0 : Real) < (N : Real) ^ 2 := by positivity
  have hkpos : 0 < k := Nat.ceil_pos.mpr (mul_pos hδpos hN2)
  let σ := Nat × (Nat → ZMod N → ZMod N) × (Nat → Finset (ZMod N)) ×
    (ZMod N → ZMod N → Finset Nat)
  let Inv : σ → Prop := fun s => PropNineThreeInvariant Γ R' s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
    k * s.1 ≤ propNineThreePotential s.2.2.2
  let Good : σ → Prop := fun s =>
    ((propNineThreeBad Γ rho η s.2.1 s.2.2.2).card : Real) < ε * (N : Real) ^ 3 ∧
    ((propNineThreeBad12 Γ rho η s.2.1 s.2.2.2).card : Real) < ε * (N : Real) ^ 11
  have hcap : ∀ s, Inv s → propNineThreePotential s.2.2.2 ≤ N * N * s₀ := by
    intro s hs
    unfold propNineThreePotential
    calc ∑ p : ZMod N × ZMod N, (s.2.2.2 p.1 p.2).card ≤ ∑ _p : ZMod N × ZMod N, s₀ :=
          Finset.sum_le_sum fun p _ => propNineThree_index_card_le Γ hΓ hs₀ hs.1 p.1 p.2
      _ = N * N * s₀ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul]
  -- a round raising the potential by `δN²` raises it by `k`
  have hraise : ∀ (s : σ) (I' : ZMod N → ZMod N → Finset Nat),
      (propNineThreePotential s.2.2.2 : Real) + δ * (N : Real) ^ 2 ≤ propNineThreePotential I' →
      propNineThreePotential s.2.2.2 + k ≤ propNineThreePotential I' := by
    intro s I' h
    have h3 : propNineThreePotential s.2.2.2 ≤ propNineThreePotential I' := by
      have : (propNineThreePotential s.2.2.2 : Real) ≤ propNineThreePotential I' := by
        have : 0 < δ * (N : Real) ^ 2 := mul_pos hδpos hN2
        linarith
      exact_mod_cast this
    have h4 : k ≤ propNineThreePotential I' - propNineThreePotential s.2.2.2 := by
      apply Nat.ceil_le.mpr
      rw [Nat.cast_sub h3]
      linarith
    omega
  have hstep : ∀ s, Inv s → ¬ Good s → ∃ s', Inv s' ∧
      propNineThreePotential s.2.2.2 + k ≤ propNineThreePotential s'.2.2.2 := by
    intro s hs hg
    have hnew : ∃ (θ' : Nat → ZMod N → ZMod N) (D' : Nat → Finset (ZMod N))
        (I' : ZMod N → ZMod N → Finset Nat),
        PropNineThreeInvariant Γ R' (s.1 + 1) θ' D' I' ∧
        (propNineThreePotential s.2.2.2 : Real) + δ * (N : Real) ^ 2 ≤
          propNineThreePotential I' := by
      by_cases h4 : ((propNineThreeBad Γ rho η s.2.1 s.2.2.2).card : Real) < ε * (N : Real) ^ 3
      · have h12 : ε * (N : Real) ^ 11 ≤ (propNineThreeBad12 Γ rho η s.2.1 s.2.2.2).card :=
          not_lt.mp fun h => hg ⟨h4, h⟩
        obtain ⟨θ', D', I', hinv', hpot⟩ := milicevic_prop_9_3_round_twelve Γ hΓ hr M hrho
          hrho1 hM hs₀ hη0 hη hε hs.1 h12
        refine ⟨θ', D', I', hinv', ?_⟩
        have : δ ≤ claimNineFiveDensity ε R d := min_le_right _ _
        nlinarith [sq_nonneg (N : Real)]
      · obtain ⟨θ', D', I', hinv', hpot⟩ := milicevic_prop_9_3_round Γ hΓ hr2 M hrho
          hrho1 hM hs₀ hη0 hη2 hε hs.1 (not_lt.mp h4)
        refine ⟨θ', D', I', hinv', ?_⟩
        have : δ ≤ claimNineFourDensity ε R d := min_le_left _ _
        nlinarith [sq_nonneg (N : Real)]
    obtain ⟨θ', D', I', hinv', hpot⟩ := hnew
    have hk' := hraise s I' hpot
    refine ⟨(s.1 + 1, θ', D', I'), ⟨hinv', ?_⟩, hk'⟩
    have := hs.2
    show k * (s.1 + 1) ≤ propNineThreePotential I'
    rw [Nat.mul_succ]
    omega
  have h0 : Inv (0, fun _ _ => 0, fun _ => ∅, fun _ _ => ∅) := by
    refine ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun x a => ?_⟩, by simp⟩
    refine ⟨Finset.empty_subset _, fun i hi => absurd hi (Finset.notMem_empty i),
      by simp, ?_⟩
    intro A hA B hB _
    rw [Finset.image_empty, Finset.subset_empty] at hA hB
    rw [hA, hB]
  obtain ⟨s, hs, hg, -⟩ := exists_good_of_potential Inv Good
    (fun s => propNineThreePotential s.2.2.2) (N * N * s₀) k hkpos hcap hstep _ h0
  exact ⟨s.1, s.2.1, s.2.2.1, s.2.2.2, hs.1, hg.1, hg.2, hs.2.trans (hcap s hs)⟩

end LeanProofs.GowersSzemeredi
