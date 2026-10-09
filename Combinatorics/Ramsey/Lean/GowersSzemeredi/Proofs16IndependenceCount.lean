import GowersSzemeredi.Definitions

/-! The independence cap of Milićević's Proposition 9.3 (arXiv:2601.01682,
printed pp. 65–66).

The iteration keeps, for each pair of indices, a set of Freiman
homomorphism values that is `{-1,0,1}`-independent and lies in a bounded
span of the two frequency sets. Independence caps the size.
* `spanBall Γ R`: the combinations `∑ n_γ γ` with `|n_γ| ≤ R`.
  `spanBall_card_le`: at most `(2R+1)^|Γ|` elements.
* `subset_sum_mem_spanBall`: a sum of at most `s` elements of
  `spanBall Γ R` lies in `spanBall Γ (sR)`.
* `independent_card_le`: if `s` elements of `spanBall Γ R` have pairwise
  distinct `{0,1}`-subset sums (implied by `{-1,0,1}`-independence), then
  `2^s ≤ (2sR+1)^|Γ|`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Integer combinations of `Γ` with coefficients in `[-R, R]`. -/
def spanBall {G : Type*} [AddCommGroup G] (Γ : Finset G) (R : Nat) : Finset G :=
  (Fintype.piFinset fun _ : Γ => Finset.Icc (-(R : Int)) R).image fun n =>
    ∑ γ : Γ, n γ • (γ : G)

theorem spanBall_card_le {G : Type*} [AddCommGroup G] (Γ : Finset G) (R : Nat) :
    (spanBall Γ R).card ≤ (2 * R + 1) ^ Γ.card := by
  unfold spanBall
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Int.card_Icc]
  congr 1
  omega

/-- Sums of at most `s` elements of `spanBall Γ R` lie in `spanBall Γ (sR)`. -/
theorem subset_sum_mem_spanBall {G : Type*} [AddCommGroup G] (Γ : Finset G) (R : Nat)
    {ι : Type*} (S : Finset ι) (v : ι → G) (hv : ∀ i ∈ S, v i ∈ spanBall Γ R) :
    ∑ i ∈ S, v i ∈ spanBall Γ (S.card * R) := by
  induction S using Finset.induction_on with
  | empty =>
    refine Finset.mem_image.mpr ⟨fun _ => 0, ?_, by simp⟩
    rw [Fintype.mem_piFinset]
    intro γ
    simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    obtain ⟨n, hn, hnv⟩ := Finset.mem_image.mp (hv a (Finset.mem_insert_self a S))
    obtain ⟨m, hm, hmv⟩ := Finset.mem_image.mp
      (ih fun i hi => hv i (Finset.mem_insert_of_mem hi))
    refine Finset.mem_image.mpr ⟨fun γ => n γ + m γ, ?_, ?_⟩
    · rw [Fintype.mem_piFinset] at hn hm ⊢
      intro γ
      have h1 := Finset.mem_Icc.mp (hn γ)
      have h2 := Finset.mem_Icc.mp (hm γ)
      rw [Finset.mem_Icc]
      push_cast at h1 h2 ⊢
      constructor <;> nlinarith
    · simp only [add_smul, Finset.sum_add_distrib]
      rw [hnv, hmv]

/-- **The independence cap.** -/
theorem independent_card_le {G : Type*} [AddCommGroup G] (Γ : Finset G) (R s : Nat)
    (v : Fin s → G) (hv : ∀ i, v i ∈ spanBall Γ R)
    (hind : Function.Injective fun ε : Fin s → Bool => ∑ i, if ε i then v i else 0) :
    2 ^ s ≤ (2 * s * R + 1) ^ Γ.card := by
  have hmem : ∀ ε : Fin s → Bool, (∑ i, if ε i then v i else 0) ∈ spanBall Γ (s * R) := by
    intro ε
    rw [← Finset.sum_filter]
    have h := subset_sum_mem_spanBall Γ R (Finset.univ.filter fun i => ε i = true) v
      (fun i _ => hv i)
    have hc : (Finset.univ.filter fun i => ε i = true).card ≤ s := by
      calc _ ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_filter_le _ _
        _ = s := by rw [Finset.card_univ, Fintype.card_fin]
    -- enlarge the radius
    obtain ⟨n, hn, hnv⟩ := Finset.mem_image.mp h
    refine Finset.mem_image.mpr ⟨n, ?_, hnv⟩
    rw [Fintype.mem_piFinset] at hn ⊢
    intro γ
    have h1 := Finset.mem_Icc.mp (hn γ)
    have hcR : ((Finset.univ.filter fun i => ε i = true).card * R : Nat) ≤ s * R :=
      Nat.mul_le_mul_right R hc
    have hcR' : (((Finset.univ.filter fun i => ε i = true).card * R : Nat) : Int) ≤
        ((s * R : Nat) : Int) := by exact_mod_cast hcR
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcard : (Finset.univ : Finset (Fin s → Bool)).card ≤ (spanBall Γ (s * R)).card := by
    apply Finset.card_le_card_of_injOn (fun ε => ∑ i, if ε i then v i else 0)
    · intro ε _; exact hmem ε
    · intro ε _ ε' _ h; exact hind h
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  calc 2 ^ s ≤ (spanBall Γ (s * R)).card := hcard
    _ ≤ (2 * (s * R) + 1) ^ Γ.card := spanBall_card_le Γ (s * R)
    _ = (2 * s * R + 1) ^ Γ.card := by ring_nf

/-- **The cap in logarithmic form:** `s ≤ |Γ|·(log₂(2sR+1) + 1)`. -/
theorem independent_card_le_log {G : Type*} [AddCommGroup G] (Γ : Finset G) (R s : Nat)
    (v : Fin s → G) (hv : ∀ i, v i ∈ spanBall Γ R)
    (hind : Function.Injective fun ε : Fin s → Bool => ∑ i, if ε i then v i else 0) :
    s ≤ Γ.card * (Nat.log 2 (2 * s * R + 1) + 1) := by
  have h := independent_card_le Γ R s v hv hind
  have hlt : 2 * s * R + 1 < 2 ^ (Nat.log 2 (2 * s * R + 1) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : (2 * s * R + 1) ^ Γ.card ≤ (2 ^ (Nat.log 2 (2 * s * R + 1) + 1)) ^ Γ.card :=
    Nat.pow_le_pow_left hlt.le _
  rw [← pow_mul] at h2
  have := h.trans h2
  rw [mul_comm] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

end LeanProofs.GowersSzemeredi
