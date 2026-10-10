import GowersSzemeredi.Proofs16ClaimNineFour
import GowersSzemeredi.Proofs16SubsetSumIndependence
import GowersSzemeredi.Proofs16IterationTools
import GowersSzemeredi.Proofs16UniformQuarterBohrSum
import GowersSzemeredi.Proofs16BoundedSpanPhase

/-! The iteration of Milićević's Proposition 9.3 in `ℤ/N`
(arXiv:2601.01682, printed pp. 65–67): "apply repeatedly Claim 9.4 until a
`1 − ε` proportion of the triples satisfy (24)".

**State.** Maps `θ_i` (`i < m`) with Freiman 8-domains `D_i`, and for each
pair `(x, a)` (Milićević's pair `(x+a, x)`) an index set `I_{x,a} ⊆ [m]`
with
* `a ∈ D_i` and `θ_i(a) ∈ ⟨Γ_{x+a} ∪ Γ_x⟩_{2R}` for `i ∈ I_{x,a}`;
* `i ↦ θ_i(a)` injective on `I_{x,a}`, with `{-1,0,1}`-independent values.

This is `PropNineThreeInvariant`.

**Bad triples.** `(x, y, a)` is bad (`propNineThreeBad`) when (24) fails:
some `d` has `|θ_i(a)·d| ≤ ηN` for all `i ∈ I_{x,a} ∪ I_{y,a}` but
`d ∉ B(Γ_{x+a} ∪ Γ_x; ρ) + B(Γ_{y+a} ∪ Γ_y; ρ)`.

**One round** (`milicevic_prop_9_3_round`). From `εN³` bad triples:
1. `escape_frequency_uniform` gives an escaping frequency in both span
   balls, with the uniform radius `R = propNineThreeRadius (2d) M ρ`.
2. `escape_split` gives `claim_9_4`'s decomposition.
3. The forbidden set is `⟨θ_i(a) : i ∈ I_{x,a}⟩_1`, by
   `spanBall_subset_boundedFrequencySpan`.
4. `claim_9_4` gives `Θ = θ_m`, which is appended to `I_{x,a}` on
   `claimNineFourDensity ε R d · N²` pairs.

**Termination** (`milicevic_prop_9_3_iteration`). The potential `∑|I_{x,a}|` is
capped at `N²s₀`, since `2^s ≤ (4sR+1)^{2d}` forces `s ≤ s₀`
(`card_le_of_subsetSumInjective`). It rises by
`k = ⌈claimNineFourDensity ε R d · N²⌉` per round, so
`exists_good_of_potential` reaches a state with fewer than `εN³` bad
triples after `m ≤ N²s₀/k` rounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The uniform spectral radius of the iteration. -/
def propNineThreeRadius (r M : Nat) (rho : Real) : Nat :=
  polynomialSpectrumCutoff r (rho / 2) (2 * bohrSumRankThreshold r r M M)

/-- **Escape with a uniform radius**: the rank-capped quarter-radius
Theorem 27 in place of the set-dependent one. -/
theorem escape_frequency_uniform {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) (r M : Nat) [NeZero M] (hK : K.card ≤ r) (hL : L.card ≤ r)
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M)
    {ι : Type*} [Fintype ι] (θ : ι → ZMod N) {η : Real}
    (hη : (Fintype.card ι : Real) * η ≤ 1 / 4)
    {d : ZMod N} (hd : ∀ i, (centeredAbs (θ i * d) : Real) ≤ η * N)
    (hnot : ¬ ∃ x ∈ bohr K rho, ∃ y ∈ bohr L rho, d = x + y) :
    ∃ ξ ∈ boundedFrequencySpan (fun k : K => (k : ZMod N)) (propNineThreeRadius r M rho) ∩
        boundedFrequencySpan (fun l : L => (l : ZMod N)) (propNineThreeRadius r M rho),
      ξ ∉ boundedFrequencySpan θ 1 := by
  by_contra hall
  push Not at hall
  apply hnot
  apply bohr_sum_contains_rank_cap_span_quarter K L r M hK hL hrho hrho1 hM d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ξ hξ => ?_⟩
  have hb := boundedFrequencySpan_phase_bound θ 1 d hd (hall ξ hξ)
  have hN : (0 : Real) ≤ N := by positivity
  calc (centeredAbs (ξ * d) : Real) ≤ Fintype.card ι * ((1 : Nat) : Real) * η * N := hb
    _ = ((Fintype.card ι : Real) * η) * N := by push_cast; ring
    _ ≤ 1 / 4 * N := mul_le_mul_of_nonneg_right hη hN

/-- The iteration invariant of Proposition 9.3. -/
def PropNineThreeInvariant {N : Nat} [NeZero N] (Γ : ZMod N → Finset (ZMod N)) (R' m : Nat)
    (θ : Nat → ZMod N → ZMod N) (D : Nat → Finset (ZMod N))
    (I : ZMod N → ZMod N → Finset Nat) : Prop :=
  (∀ i < m, FreimanHom 8 (D i) (θ i)) ∧
    ∀ x a, I x a ⊆ Finset.range m ∧
      (∀ i ∈ I x a, a ∈ D i ∧ θ i a ∈ spanBall (Γ (x + a) ∪ Γ x) R') ∧
      Set.InjOn (fun i => θ i a) ↑(I x a) ∧
      SubsetSumInjective ((I x a).image fun i => θ i a)

/-- The triples `(x, y, a)` on which containment (24) fails. -/
def propNineThreeBad {N : Nat} [NeZero N] (Γ : ZMod N → Finset (ZMod N)) (rho η : Real)
    (θ : Nat → ZMod N → ZMod N) (I : ZMod N → ZMod N → Finset Nat) :
    Finset (ZMod N × ZMod N × ZMod N) :=
  Finset.univ.filter fun t => ∃ d : ZMod N,
    (∀ i ∈ I t.1 t.2.2 ∪ I t.2.1 t.2.2, (centeredAbs (θ i t.2.2 * d) : Real) ≤ η * N) ∧
    ¬ ∃ u ∈ bohr (Γ (t.1 + t.2.2) ∪ Γ t.1) rho,
      ∃ v ∈ bohr (Γ (t.2.1 + t.2.2) ∪ Γ t.2.1) rho, d = u + v

/-- The potential `∑_{x,a} |I_{x,a}|`. -/
def propNineThreePotential {N : Nat} [NeZero N] (I : ZMod N → ZMod N → Finset Nat) : Nat :=
  ∑ p : ZMod N × ZMod N, (I p.1 p.2).card

/-- **The cap**: every index set has at most `s₀` elements. -/
theorem propNineThree_index_card_le {N : Nat} [NeZero N] (Γ : ZMod N → Finset (ZMod N))
    {d R' m s₀ : Nat} (hΓ : ∀ z, (Γ z).card ≤ d)
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * R' + 1) ^ (2 * d) → s ≤ s₀)
    {θ : Nat → ZMod N → ZMod N} {D : Nat → Finset (ZMod N)} {I : ZMod N → ZMod N → Finset Nat}
    (hinv : PropNineThreeInvariant Γ R' m θ D I) (x a : ZMod N) : (I x a).card ≤ s₀ := by
  obtain ⟨-, hI, hinj, hind⟩ := hinv.2 x a
  set V := (I x a).image fun i => θ i a with hV
  have hVcard : V.card = (I x a).card := Finset.card_image_of_injOn hinj
  have hVsub : V ⊆ spanBall (Γ (x + a) ∪ Γ x) R' := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (hI i hi).2
  have h := card_le_of_subsetSumInjective _ R' hVsub hind
  have hcard : (Γ (x + a) ∪ Γ x).card ≤ 2 * d :=
    (Finset.card_union_le _ _).trans (by have := hΓ (x + a); have := hΓ x; omega)
  apply hs₀
  rw [← hVcard]
  exact h.trans (Nat.pow_le_pow_right (by omega) hcard)

/-- **One round of Proposition 9.3.** -/
theorem milicevic_prop_9_3_round {N : Nat} [NeZero N] [Fact N.Prime] (Γ : ZMod N → Finset (ZMod N))
    {d : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) (M : Nat) [NeZero M] {rho : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius (2 * d) M rho) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 2 * (s₀ : Real) * η ≤ 1 / 4) {ε : Real} (hε : 0 < ε)
    {m : Nat} {θ : Nat → ZMod N → ZMod N} {D : Nat → Finset (ZMod N)}
    {I : ZMod N → ZMod N → Finset Nat}
    (hinv : PropNineThreeInvariant Γ (2 * propNineThreeRadius (2 * d) M rho) m θ D I)
    (hbad : ε * (N : Real) ^ 3 ≤ (propNineThreeBad Γ rho η θ I).card) :
    ∃ (θ' : Nat → ZMod N → ZMod N) (D' : Nat → Finset (ZMod N))
      (I' : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ (2 * propNineThreeRadius (2 * d) M rho) (m + 1) θ' D' I' ∧
      (propNineThreePotential I : Real) +
          claimNineFourDensity ε (propNineThreeRadius (2 * d) M rho) d * (N : Real) ^ 2 ≤
        propNineThreePotential I' := by
  set R := propNineThreeRadius (2 * d) M rho with hRdef
  set Bad := propNineThreeBad Γ rho η θ I with hBad
  have hcap := propNineThree_index_card_le Γ hΓ hs₀ hinv
  -- the decompositions on the bad triples
  have key : ∀ t : ZMod N × ZMod N × ZMod N, ∃ ξ4 : Fin 4 → ZMod N, t ∈ Bad →
      (ξ4 0 ∈ spanBall (Γ (t.1 + t.2.2)) R ∧ ξ4 1 ∈ spanBall (Γ t.1) R ∧
        ξ4 2 ∈ spanBall (Γ (t.2.1 + t.2.2)) R ∧ ξ4 3 ∈ spanBall (Γ t.2.1) R) ∧
      ξ4 0 - ξ4 1 = ξ4 2 - ξ4 3 ∧
      ξ4 0 - ξ4 1 ∉ spanBall ((I t.1 t.2.2).image fun i => θ i t.2.2) 1 := by
    intro t
    by_cases ht : t ∈ Bad
    · obtain ⟨-, dd, hdd, hnot⟩ := Finset.mem_filter.mp ht
      set W := (I t.1 t.2.2 ∪ I t.2.1 t.2.2).image fun i => θ i t.2.2 with hW
      have hWcard : (Fintype.card W : Real) * η ≤ 1 / 4 := by
        rw [Fintype.card_coe]
        have h1 : W.card ≤ 2 * s₀ := by
          refine (Finset.card_image_le).trans ((Finset.card_union_le _ _).trans ?_)
          have := hcap t.1 t.2.2
          have := hcap t.2.1 t.2.2
          omega
        have h2 : (W.card : Real) ≤ 2 * s₀ := by exact_mod_cast h1
        nlinarith
      have hWd : ∀ w : W, (centeredAbs ((w : ZMod N) * dd) : Real) ≤ η * N := by
        intro w
        obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp w.2
        rw [← hiw]
        exact hdd i hi
      have hK : (Γ (t.1 + t.2.2) ∪ Γ t.1).card ≤ 2 * d :=
        (Finset.card_union_le _ _).trans (by have := hΓ (t.1 + t.2.2); have := hΓ t.1; omega)
      have hL : (Γ (t.2.1 + t.2.2) ∪ Γ t.2.1).card ≤ 2 * d :=
        (Finset.card_union_le _ _).trans
          (by have := hΓ (t.2.1 + t.2.2); have := hΓ t.2.1; omega)
      obtain ⟨ξ, hξKL, hξesc⟩ := escape_frequency_uniform _ _ (2 * d) M hK hL hrho hrho1 hM
        (fun w : W => (w : ZMod N)) hWcard hWd hnot
      obtain ⟨hξK, hξL⟩ := Finset.mem_inter.mp hξKL
      obtain ⟨ξ₀, h₀, ξ₁, h₁, ξ₂, h₂, ξ₃, h₃, hξ, hdec⟩ :=
        escape_split Γ t.1 t.2.1 t.2.2 le_rfl le_rfl hξK hξL
      refine ⟨![ξ₀, ξ₁, ξ₂, ξ₃], fun _ => ⟨⟨h₀, h₁, h₂, h₃⟩, hdec, ?_⟩⟩
      show ξ₀ - ξ₁ ∉ _
      rw [← hξ]
      intro hmem
      apply hξesc
      refine spanBall_subset_boundedFrequencySpan ?_ 1 hmem
      exact Finset.image_subset_image Finset.subset_union_left
    · exact ⟨0, fun h => absurd h ht⟩
  choose ξ hξ using key
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨Θ, B, P, hF, hPcard, hP⟩ := claim_9_4 Γ hΓ Bad ξ (fun t ht => (hξ t ht).1)
    (fun t ht => (hξ t ht).2.1)
    (fun x a => spanBall ((I x a).image fun i => θ i a) 1) (fun t ht => (hξ t ht).2.2)
    hε hbad
  -- the updated state
  let θ' : Nat → ZMod N → ZMod N := fun i => if i = m then Θ else θ i
  let D' : Nat → Finset (ZMod N) := fun i => if i = m then B else D i
  let I' : ZMod N → ZMod N → Finset Nat := fun x a =>
    if (x, a) ∈ P then insert m (I x a) else I x a
  have hlt : ∀ x a, ∀ i ∈ I x a, i ≠ m := by
    intro x a i hi
    have := Finset.mem_range.mp ((hinv.2 x a).1 hi)
    omega
  have himage : ∀ x a, (I x a).image (fun i => θ' i a) = (I x a).image (fun i => θ i a) := by
    intro x a
    refine Finset.image_congr fun i hi => ?_
    simp only [θ', if_neg (hlt x a i hi)]
  refine ⟨θ', D', I', ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    by_cases him : i = m
    · simp only [θ', D', if_pos him]
      exact hF
    · simp only [θ', D', if_neg him]
      exact hinv.1 i (by omega)
  · intro x a
    obtain ⟨hsub, hI, hinj, hind⟩ := hinv.2 x a
    by_cases hp : (x, a) ∈ P
    · obtain ⟨haB, hΘspan, hΘnot⟩ := hP (x, a) hp
      simp only [I', if_pos hp]
      have hΘnotV : Θ a ∉ (I x a).image fun i => θ i a :=
        fun h => hΘnot (self_mem_spanBall_one h)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hsub hi)))
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp only [θ', D', if_pos rfl]
          exact ⟨haB, hΘspan⟩
        · simp only [θ', D', if_neg (hlt x a i hi)]
          exact hI i hi
      · rw [Finset.coe_insert, Set.injOn_insert (fun h => hlt x a m h rfl)]
        refine ⟨?_, ?_⟩
        · intro i hi j hj hij
          simp only [θ', if_neg (hlt x a i hi), if_neg (hlt x a j hj)] at hij
          exact hinj hi hj hij
        · rintro ⟨i, hi, hij⟩
          simp only [θ', if_neg (hlt x a i hi), if_pos rfl] at hij
          exact hΘnotV (Finset.mem_image.mpr ⟨i, hi, hij⟩)
      · rw [Finset.image_insert, himage x a]
        simp only [θ', if_pos rfl]
        exact subsetSumInjective_insert hind hΘnot
    · simp only [I', if_neg hp]
      refine ⟨hsub.trans (Finset.range_mono (Nat.le_succ m)), ?_, ?_, ?_⟩
      · intro i hi
        simp only [θ', D', if_neg (hlt x a i hi)]
        exact hI i hi
      · intro i hi j hj hij
        simp only [θ', if_neg (hlt x a i hi), if_neg (hlt x a j hj)] at hij
        exact hinj hi hj hij
      · rw [himage x a]
        exact hind
  · -- the potential rises by `|P|`
    have hpot : propNineThreePotential I' = propNineThreePotential I + P.card := by
      unfold propNineThreePotential
      have : ∀ p : ZMod N × ZMod N, (I' p.1 p.2).card =
          (I p.1 p.2).card + if p ∈ P then 1 else 0 := by
        intro p
        by_cases hp : p ∈ P
        · have hp' : (p.1, p.2) ∈ P := hp
          simp only [I', if_pos hp']
          exact Finset.card_insert_of_notMem fun h => hlt p.1 p.2 m h rfl
        · have hp' : (p.1, p.2) ∉ P := hp
          simp only [I', if_neg hp', if_neg hp, add_zero]
      rw [Finset.sum_congr rfl fun p _ => this p, Finset.sum_add_distrib]
      congr 1
      simp [Finset.sum_boole, Finset.filter_mem_eq_inter]
    rw [hpot]
    push_cast
    linarith

/-- **The iteration of Proposition 9.3 terminates.** Starting from the empty
state, Claim 9.4 rounds reach a state with fewer than `εN³` bad triples. The
number `m` of maps satisfies `⌈δN²⌉·m ≤ N²s₀`, with
`δ = claimNineFourDensity ε R d`. -/
theorem milicevic_prop_9_3_iteration {N : Nat} [NeZero N] [Fact N.Prime] (Γ : ZMod N → Finset (ZMod N))
    {d : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) (M : Nat) [NeZero M] {rho : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius (2 * d) M rho) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 2 * (s₀ : Real) * η ≤ 1 / 4) {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (θ : Nat → ZMod N → ZMod N) (D : Nat → Finset (ZMod N))
      (I : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ (2 * propNineThreeRadius (2 * d) M rho) m θ D I ∧
      ((propNineThreeBad Γ rho η θ I).card : Real) < ε * (N : Real) ^ 3 ∧
      ⌈claimNineFourDensity ε (propNineThreeRadius (2 * d) M rho) d * (N : Real) ^ 2⌉₊ * m ≤
        N * N * s₀ := by
  set R' := 2 * propNineThreeRadius (2 * d) M rho with hR'
  set δ := claimNineFourDensity ε (propNineThreeRadius (2 * d) M rho) d with hδ
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hδpos : 0 < δ := by
    simp only [hδ, claimNineFourDensity]
    have : (0 : Real) < (((2 * propNineThreeRadius (2 * d) M rho + 1) ^ d : Nat) : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (by positivity)
    positivity
  set k := ⌈δ * (N : Real) ^ 2⌉₊ with hk
  have hkpos : 0 < k := Nat.ceil_pos.mpr (by positivity)
  let σ := Nat × (Nat → ZMod N → ZMod N) × (Nat → Finset (ZMod N)) × (ZMod N → ZMod N → Finset Nat)
  let Inv : σ → Prop := fun s => PropNineThreeInvariant Γ R' s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
    k * s.1 ≤ propNineThreePotential s.2.2.2
  let Good : σ → Prop := fun s =>
    ((propNineThreeBad Γ rho η s.2.1 s.2.2.2).card : Real) < ε * (N : Real) ^ 3
  have hcap : ∀ s, Inv s → propNineThreePotential s.2.2.2 ≤ N * N * s₀ := by
    intro s hs
    unfold propNineThreePotential
    calc ∑ p : ZMod N × ZMod N, (s.2.2.2 p.1 p.2).card ≤ ∑ _p : ZMod N × ZMod N, s₀ :=
          Finset.sum_le_sum fun p _ => propNineThree_index_card_le Γ hΓ hs₀ hs.1 p.1 p.2
      _ = N * N * s₀ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul]
  have hstep : ∀ s, Inv s → ¬ Good s → ∃ s', Inv s' ∧
      propNineThreePotential s.2.2.2 + k ≤ propNineThreePotential s'.2.2.2 := by
    intro s hs hg
    have hbad : ε * (N : Real) ^ 3 ≤ (propNineThreeBad Γ rho η s.2.1 s.2.2.2).card :=
      not_lt.mp hg
    obtain ⟨θ', D', I', hinv', hpot⟩ :=
      milicevic_prop_9_3_round Γ hΓ M hrho hrho1 hM hs₀ hη0 hη hε hs.1 hbad
    have hk' : propNineThreePotential s.2.2.2 + k ≤ propNineThreePotential I' := by
      have h2 : δ * (N : Real) ^ 2 ≤
          (propNineThreePotential I' : Real) - propNineThreePotential s.2.2.2 := by linarith
      have h3 : propNineThreePotential s.2.2.2 ≤ propNineThreePotential I' := by
        have : (propNineThreePotential s.2.2.2 : Real) ≤ propNineThreePotential I' := by
          have : 0 < δ * (N : Real) ^ 2 := by positivity
          linarith
        exact_mod_cast this
      have h4 : k ≤ propNineThreePotential I' - propNineThreePotential s.2.2.2 := by
        apply Nat.ceil_le.mpr
        rw [Nat.cast_sub h3]
        exact h2
      omega
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
  obtain ⟨s, hs, hg, -⟩ := exists_good_of_potential Inv Good (fun s => propNineThreePotential s.2.2.2)
    (N * N * s₀) k hkpos hcap hstep _ h0
  exact ⟨s.1, s.2.1, s.2.2.1, s.2.2.2, hs.1, hg, hs.2.trans (hcap s hs)⟩

end LeanProofs.GowersSzemeredi
