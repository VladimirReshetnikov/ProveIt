import GowersSzemeredi.Proofs18CoverSharper

/-! **Theorem 18.1 at `d + 7` and Theorem 18.2 at `L + 5` for `L ≥ 11`**:
a tighter base budget (Notes L.15a).

The joint-cover step costs `68·2^k` (the vertex covers), `μ₀` (the base
budget of the cover controls) and `136·2^k` (the two slice controls) in the
log-degree. The standard parameters take `μ₀ = genMu0 k ≈ 2^(k+6)`, from the
bound `V ≤ 2^(2^(2^(k+6)))` on the class base `V = classV`. But every summand
of `classV k` is at most `2^(2^(2^(k+4)))`, so `V ≤ 2^(2^(2^(k+4)+1))`
(`classV_le_tight`), and `μ₀ = tightMu0 k = 2^(k+5) + 9` suffices (it is then
set by `fixDeg k = 2^(k+5) + 7`). One step costs `236·2^k + O(k²)`
(`envStepC_le_tight`), so the envelopes grow like `472·2^k < 512·2^k`:
* `polyGenMuT_le`: `polyGenMuT k ≤ 500·2^k` for `k ≥ 4` (and the degrees
  `4, 5` by evaluation), giving **Theorem 18.1 at every degree `d ≥ 4` with
  exponent `α^(2^(2^(d+7)))`** (`theorem_18_1_d7_of_profiles_cover`);
* `genMuT_le`: `genMuT k ≤ 505·2^k` for `k ≥ 7`, giving **Theorem 18.2 at
  every length `L ≥ 11` with `L + 5`** (`theorem_18_2_L5_of_profiles_cover`).
  Below `L = 11` the cubic stopping term `40(k+2)³ + 1095` exceeds `2^(L+5)`.
`d + 6` and `L + 4` would need a step cost below `128·2^k`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The tight log-log bound of the class base. -/
def tightMuV (k : Nat) : Nat := 2 ^ (k + 4) + 1

/-- The tight base budget. -/
def tightMu0 (k : Nat) : Nat := max (tightMuV k) (fixDeg k) + 2

/-- **The class base is at most `2^(2^(2^(k+4)+1))`.** -/
theorem classV_le_tight (Kc pc : Nat → Nat)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) (k : Nat) :
    classV Kc pc k ≤ 2 ^ (2 ^ tightMuV k) := by
  set E := (2 : Nat) ^ ((2 : Nat) ^ (k + 4)) with hE
  have hterm : ∀ j ∈ Finset.range k, (Kc j : Real) + pc j ≤ 2 ^ E := by
    intro j hj
    have hjk : j + 5 ≤ k + 4 := by have := Finset.mem_range.mp hj; omega
    refine (hconst j).trans (pow_le_pow_right₀ (by norm_num) ?_)
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hjk)
  have hsum : ∑ j ∈ Finset.range k, ((Kc j : Real) + pc j) ≤ k * 2 ^ E := by
    have := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hE1 : (1 : Real) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hk1 : ((k : Real) + 1) ≤ 2 ^ (k + 1) := by
    have h : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    exact_mod_cast h.le
  have hkE : k + 1 + E ≤ 2 ^ tightMuV k := by
    have h1 : k + 4 < 2 ^ (k + 4) := Nat.lt_two_pow_self
    have h2 : 2 ^ (k + 4) < E := Nat.lt_two_pow_self
    have h3 : 2 ^ tightMuV k = 2 * E := by
      unfold tightMuV; rw [pow_succ, hE]; ring
    omega
  calc classV Kc pc k ≤ ((k : Real) + 1) * 2 ^ E := by
        unfold classV
        nlinarith
    _ ≤ 2 ^ (k + 1) * 2 ^ E := mul_le_mul_of_nonneg_right hk1 (by positivity)
    _ = 2 ^ (k + 1 + E) := by rw [pow_add (2 : Real) (k + 1) E]
    _ ≤ 2 ^ (2 ^ tightMuV k) := pow_le_pow_right₀ (by norm_num) hkE

/-- The standing hypotheses at the tight base budget. -/
theorem tightHyp_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) {k : Nat}
    (hk : 2 ≤ k) :
    (⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩ : GenParamsC).CHyp (tightMuV k) (genMuK k) := by
  obtain ⟨hV, -, -, -, -, -, hKk, hKμ, hpk, hpμ⟩ := stdHyp_of_profiles Kc pc hK hp hconst hk
  refine ⟨hV, classV_le_tight Kc pc hconst k, le_rfl, ?_, hKk, hKμ, hpk, hpμ⟩
  show k ≤ 2 ^ tightMu0 k
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ tightMu0 k := Nat.pow_le_pow_right (by norm_num) (by
        unfold tightMu0 fixDeg; have := Nat.lt_two_pow_self (n := k + 5)
        have := le_max_right (tightMuV k) (2 ^ (k + 5) + 7); omega)

/-! ### The envelopes at the tight base budget -/

/-- The Theorem 18.1 envelope at the tight base budget. -/
def polyGenMuT : Nat → Nat
  | 0 => 74
  | 1 => 74
  | k + 2 => envStepC (k + 2) (tightMu0 (k + 2)) (genMuK (k + 2)) (polyGenMuT (k + 1))

theorem polyGenMuT_succ {k : Nat} (hk : 1 ≤ k) :
    polyGenMuT (k + 1) = envStepC (k + 1) (tightMu0 (k + 1)) (genMuK (k + 1)) (polyGenMuT k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

/-- The Theorem 18.2 envelope at the tight base budget. -/
def genMuT : Nat → Nat
  | 0 => 62
  | 1 => 62
  | k + 2 => envStepCT (k + 2) (tightMu0 (k + 2)) (genMuK (k + 2)) (genMuT (k + 1))

theorem genMuT_succ {k : Nat} (hk : 1 ≤ k) :
    genMuT (k + 1) = envStepCT (k + 1) (tightMu0 (k + 1)) (genMuK (k + 1)) (genMuT k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rfl

theorem polyEnvBound_allT (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64)) :
    ∀ k, 2 ≤ k → PolyEnvBound (k + 2) (polyGenMuT k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, PolyEnvBound (k + 1) μ →
      PolyEnvBound (k + 2) (envStepC k (tightMu0 k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsC := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_class68 Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact polyEnvBound_stepC P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    exact hstep 2 le_rfl 74 (polyEnvBound_three_of_phase_partition hpp hpφ hKφ hpφB)
  | succ k hk ih =>
    rw [polyGenMuT_succ (by omega)]
    exact hstep (k + 1) (by omega) (polyGenMuT k) ih

theorem envBound_allT (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) :
    ∀ k, 2 ≤ k → EnvBound (k + 2) (genMuT k) := by
  have hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))) :=
    fun k hk => abstractFamilyLemma166At_of k (hK k) (hp k) (hrec k hk)
  have hK1 : ∀ k, 1 ≤ Kc k := fun k => le_trans (by norm_num) (hK k)
  have hstep : ∀ k, 2 ≤ k → ∀ μ, EnvBound (k + 1) μ →
      EnvBound (k + 2) (envStepCT k (tightMu0 k) (genMuK k) μ) := by
    intro k hk μ hlow
    let P : GenParamsC := ⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩
    have H : P.CHyp (tightMuV k) (genMuK k) := tightHyp_of_profiles Kc pc hK hp hconst hk
    have hcov : ∀ l, 1 ≤ l → l ≤ P.k →
        PolyCoverAt l (uCount P.V (uDeg68 l)) (uExp P.V (uDeg68 l)) := by
      intro l hl1 hlk
      have hcl := polyCoverAt_class68 Kc pc hK1 hp hlem hl1
      exact hcl.uniform_mono (one_le_classV Kc pc l) (classV_mono Kc pc hlk) le_rfl
    exact envBound_stepC P H (by show 1 ≤ k; omega) hcov (hrec k (by omega)) hlow
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hstep 2 le_rfl 62 envBound_three
  | succ k hk ih =>
    rw [genMuT_succ (by omega)]
    exact hstep (k + 1) (by omega) (genMuT k) ih

/-! ### Closed forms -/

theorem two_pow_four_mul (k : Nat) : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring

/-- One step at the tight base budget costs `236·2^k` plus a polynomial. -/
theorem envStepC_le_tight (k μ : Nat) :
    envStepC k (tightMu0 k) (genMuK k) μ ≤ μ + 236 * 2 ^ k + 4 * (k + 3) ^ 2 + k + 39 := by
  unfold envStepC GenParamsC.densDegC GenParamsC.expDegC GenParamsC.rhoDegC tightMu0 tightMuV
    genMuK fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

theorem envStepCT_le_tight (k μ : Nat) :
    envStepCT k (tightMu0 k) (genMuK k) μ ≤
      max (μ + 236 * 2 ^ k + 4 * (k + 3) ^ 2 + k + 39) (40 * (k + 2) ^ 3 + 1095) := by
  unfold envStepCT GenParamsC.densDegC GenParamsC.threshDegC GenParamsC.expDegC
    GenParamsC.rhoDegC tightMu0 tightMuV genMuK fixDeg
  rw [two_pow_six_mul, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize 4 * (k + 3) ^ 2 = q
  generalize 40 * (k + 2) ^ 3 = c
  generalize 2 ^ k = x at *
  omega

theorem envStepCT_ge_tight (k μ : Nat) :
    μ + 236 * 2 ^ k ≤ envStepCT k (tightMu0 k) (genMuK k) μ := by
  unfold envStepCT GenParamsC.densDegC GenParamsC.rhoDegC tightMu0 tightMuV fixDeg
  rw [two_pow_five_mul, two_pow_four_mul]
  generalize 4 * (k + 3) ^ 2 = q
  generalize 2 ^ k = x at *
  omega

/-- `(k+4)² ≤ 4·2^k` for `k ≥ 4`. -/
theorem sq_le_two_pow_four : ∀ k, 4 ≤ k → (k + 4) ^ 2 ≤ 4 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 4) ^ 2 ≤ 2 * (k + 4) ^ 2 := by nlinarith
    calc (k + 1 + 4) ^ 2 ≤ 2 * (k + 4) ^ 2 := hstep
      _ ≤ 2 * (4 * 2 ^ k) := Nat.mul_le_mul_left _ ih
      _ = 4 * 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- `(k+3)³ ≤ 8·2^k` for `k ≥ 7`. -/
theorem cube_le_two_pow_seven : ∀ k, 7 ≤ k → (k + 3) ^ 3 ≤ 8 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 3) ^ 3 ≤ 2 * (k + 3) ^ 3 := by nlinarith [sq_nonneg (k : Nat)]
    calc (k + 1 + 3) ^ 3 ≤ 2 * (k + 3) ^ 3 := hstep
      _ ≤ 2 * (8 * 2 ^ k) := Nat.mul_le_mul_left _ ih
      _ = 8 * 2 ^ (k + 1) := by rw [pow_succ]; ring

theorem polyGenMuT_small : polyGenMuT 2 + 1 ≤ 2 ^ (4 + 7) ∧ polyGenMuT 3 + 1 ≤ 2 ^ (5 + 7) ∧
    polyGenMuT 4 ≤ 500 * 2 ^ 4 := by
  decide

/-- **The Theorem 18.1 envelope at the tight base budget is `≤ 500·2^k`**, `k ≥ 4`. -/
theorem polyGenMuT_le : ∀ k, 4 ≤ k → polyGenMuT k ≤ 500 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact polyGenMuT_small.2.2
  | succ k hk ih =>
    rw [polyGenMuT_succ (by omega)]
    have h1 := envStepC_le_tight (k + 1) (polyGenMuT k)
    have h2 := sq_le_two_pow_four k hk
    have h3 : 16 ≤ 2 ^ k := le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hk)
    have h4 := Nat.lt_two_pow_self (n := k)
    rw [show k + 1 + 3 = k + 4 by ring] at h1
    rw [pow_succ] at h1 ⊢
    generalize (k + 4) ^ 2 = s at *
    generalize 2 ^ k = x at *
    omega

theorem genMuT_seven : genMuT 7 ≤ 505 * 2 ^ 7 := by decide

/-- **The Theorem 18.2 envelope at the tight base budget is `≤ 505·2^k`**, `k ≥ 7`. -/
theorem genMuT_le : ∀ k, 7 ≤ k → genMuT k ≤ 505 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact genMuT_seven
  | succ k hk ih =>
    rw [genMuT_succ (by omega)]
    have h1 := envStepCT_le_tight (k + 1) (genMuT k)
    have h2 := sq_le_two_pow_four k (by omega)
    have h3 := cube_le_two_pow_seven k hk
    have h5 : 128 ≤ 2 ^ k := le_trans (by norm_num : 128 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by norm_num) hk)
    have h4 := Nat.lt_two_pow_self (n := k)
    rw [show k + 1 + 3 = k + 4 by ring, show k + 1 + 2 = k + 3 by ring] at h1
    rw [pow_succ] at h1 ⊢
    refine h1.trans (max_le ?_ ?_)
    · generalize (k + 4) ^ 2 = s at *
      generalize 2 ^ k = x at *
      omega
    · generalize (k + 3) ^ 3 = s at *
      generalize 2 ^ k = x at *
      omega

theorem genMuT_ge : ∀ k, 2 ≤ k → 236 * 2 ^ k ≤ genMuT k := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [genMuT_succ (by omega)]
  have := envStepCT_ge_tight (j + 1) (genMuT j)
  omega

/-- **Theorem 18.1 at every degree `d ≥ 4` with exponent `α^(2^(2^(d+7)))`**,
from the recurrence profiles and a phase partition. -/
theorem theorem_18_1_d7_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {Kφ : Real} {pφ : Nat} (hpp : ProgressionPhasePartition Kφ pφ) (hpφ : 0 < pφ)
    (hKφ : Kφ ≤ 2 ^ pφ) (hpφB : (pφ : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 64))
    {d : Nat} (hd4 : 4 ≤ d) : Theorem181AtSharp 7 d := by
  have henv := polyEnvBound_allT Kc pc hK hp hrec hconst hpp hpφ hKφ hpφB (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  rcases Nat.lt_or_ge d 6 with h | h
  · obtain ⟨h4, h5, -⟩ := polyGenMuT_small
    interval_cases d
    · exact h4
    · exact h5
  · have hle := polyGenMuT_le (d - 2) (by omega)
    have h2 : 2 ^ (d + 7) = 512 * 2 ^ (d - 2) := by
      rw [show d + 7 = (d - 2) + 9 by omega, pow_add]; ring
    rw [h2]
    have := Nat.one_le_two_pow (n := d - 2)
    omega

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 5` in the threshold**,
from the recurrence profiles. -/
theorem theorem_18_2_L5_of_profiles_cover (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k)
    (hp : ∀ k, 0 < pc k)
    (hrec : ∀ k, 1 ≤ k →
      Section16RecurrenceProfileWith k (familyRecThr k (Kc k) (pc k)) (familyRecExp k (pc k)))
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))
    {L : Nat} (hL11 : 11 ≤ L) : Theorem182AtSharp 5 L := by
  have henv := envBound_allT Kc pc hK hp hrec hconst (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hle := genMuT_le (L - 4) (by omega)
  have hge := genMuT_ge (L - 4) (by omega)
  have hk := Nat.lt_two_pow_self (n := L - 4)
  have h128 : 128 ≤ 2 ^ (L - 4) :=
    le_trans (by norm_num : 128 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h42 : 42 ≤ genMuT (L - 4) := by omega
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuT (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuT (L - 4))
    omega
  have h2 : 2 ^ (L + 5) = 512 * 2 ^ (L - 4) := by
    rw [show L + 5 = (L - 4) + 9 by omega, pow_add]; ring
  refine theorem182AtSharp_of_envBound (by omega) henv h42 hLμ ?_
  rw [h2]
  omega

end LeanProofs.GowersSzemeredi
