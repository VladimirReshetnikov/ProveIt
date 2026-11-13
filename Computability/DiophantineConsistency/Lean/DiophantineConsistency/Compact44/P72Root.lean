import DiophantineConsistency.Compact44.P72Graph
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011
import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
import DiophantineConsistency.ArithmeticModularCancellation

/-! # P13, sections 4 and 5: the fixed congruence and the first root

§4. `As = 0` says `Nf² = b²(1+ΔI²)` with `Nf = 3βf0 + q − β − 1 > 0`. A
rational square root of an integer is an integer, so `Nf = 3β·f`. Hence
`q = 1 + β(3j+1)` with `j = f − f0`, and `f² = 1 + ΔI²` (the normalized strong
norm), where `I = c²i`.

§5. `A0 = 0` says `Z² = M0²·n` with `M0 = q³(q−1)`. So `M0 ∣ |Z|`, and
the positive and negative parts of `Z` agree modulo `M0`. Modulo `q³` this
gives `q³ ∣ Y`. Cancelling `q³` gives `qF ≡ (X + K0·q)·C (mod q−1)`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P72Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveQuotients2011 P72Graph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub {a b : V} (h : b ≤ a) : ι (a - b) = ι a - ι b := by
  rw [eq_sub_iff_add_eq, ← map_add, tsub_add_cancel_of_le h]

theorem ι_magnitude_sq (P N : V) :
    ι (magnitude (P, N)) * ι (magnitude (P, N)) = (ι P - ι N) * (ι P - ι N) := by
  rcases le_total N P with h | h
  · have h0 : N - P = 0 := tsub_eq_zero_of_le h
    simp only [magnitude, h0, add_zero]
    rw [ι_tsub h]
  · have h0 : P - N = 0 := tsub_eq_zero_of_le h
    simp only [magnitude, h0, zero_add]
    rw [ι_tsub h]
    ring

theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4) :
    (((fun j => (p j : ℤ)) j : ℤ) : DiffRing V) = ι (p j : V) := by
  simp

/-- §4: the strong residual recovers the fixed congruence on `q`. -/
theorem strong_root (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hb : 0 < (p 0 : V))
    (hz : InternalZero (graph (fun j => (p j : ℤ))).As v) :
    let q : V := v 0 + (v 2 + v 1)
    let k : V := v 9 + v 10
    let c : V := v 9 + v 7 * k
    let a : V := v 6 * v 7 + v 7
    let Δ : V := (3 + 4 * a) + a * a
    let I : V := (c * c) * v 4
    ∃ f j : V, f = v 3 + j ∧ q = 1 + (p 0 : V) * (3 * j + 1) ∧ f * f = 1 + Δ * (I * I) := by
  intro q k c a Δ I
  let β : V := p 0
  have hβ1 : 1 ≤ β := pos_iff_one_le.mp hb
  have hNfle : β + 1 ≤ 3 * β * v 3 + q := by
    have h3 : β + 1 ≤ 3 * β := by
      calc β + 1 ≤ β + β := by simpa using hβ1
        _ ≤ 3 * β := by
          have : β + β = 2 * β := by ring
          rw [this]; exact mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
    calc β + 1 ≤ 3 * β := h3
      _ ≤ 3 * β * v 3 := le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 3))
      _ ≤ 3 * β * v 3 + q := le_add_of_nonneg_right (Arithmetic.zero_le _)
  let Nf : V := 3 * β * v 3 + q - (β + 1)
  rw [internalZero_iff, As_eval] at hz
  have hNf : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nf = ι Nf := by
    have e : ι Nf = ι (3 * β * v 3 + q) - ι (β + 1) := ι_tsub hNfle
    rw [e]
    simp only [vals, q, β, map_add, map_mul, map_one, map_ofNat, cast_port]
    ring
  have hD : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta = ι Δ := by
    simp only [vals, Δ, a, map_add, map_mul, map_ofNat]
  have hI : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I = ι I := by
    simp only [vals, I, c, k, map_add, map_mul]
  rw [hNf, hD, hI] at hz
  have hcast : ((p 0 : ℤ) : DiffRing V) = ι β := by simp [β]
  rw [hcast] at hz
  have hV : Nf * Nf = (3 * β) * (3 * β) * (1 + Δ * (I * I)) := by
    apply ι_injective
    simp only [map_mul, map_add, map_one, map_ofNat]
    linear_combination hz
  have h3β : 0 < 3 * β := mul_pos (by norm_num) hb
  obtain ⟨f, hf, hff⟩ := scaled_quotient (3 * β) Nf (1 + Δ * (I * I)) h3β hV
  have hsum : 3 * β * v 3 + q = (β + 1) + 3 * β * f := by
    rw [← hf]; exact (add_tsub_cancel_of_le hNfle).symm
  have hge : v 3 ≤ f := by
    by_contra hlt
    have hlt' : f + 1 ≤ v 3 := lt_iff_succ_le.mp (lt_of_not_ge hlt)
    have hq1 : 1 ≤ q := pos_iff_one_le.mp (add_pos_of_pos_of_nonneg (hv 0) (Arithmetic.zero_le _))
    have hb' : (1 : DiffRing V) ≤ ι β := by simpa using (ι_le_ι (V := V)).mpr hβ1
    have hq' : (1 : DiffRing V) ≤ ι q := by simpa using (ι_le_ι (V := V)).mpr hq1
    have hf' : ι f + 1 ≤ ι (v 3) := by simpa using (ι_le_ι (V := V)).mpr hlt'
    have hs := congrArg ι hsum
    simp only [map_add, map_mul, map_one, map_ofNat] at hs
    nlinarith [mul_nonneg (le_trans zero_le_one hb') (sub_nonneg.mpr hf')]
  obtain ⟨j, hj⟩ : ∃ j, f = v 3 + j := ⟨f - v 3, (add_tsub_cancel_of_le hge).symm⟩
  refine ⟨f, j, hj, ?_, hff⟩
  rw [hj] at hsum
  have : 3 * β * v 3 + q = 3 * β * v 3 + (1 + β * (3 * j + 1)) := by
    rw [hsum]; ring
  exact add_left_cancel this

/-- §5: the first residual forces `q³ ∣ Y`, the transport congruence and the
first Pell norm. -/
theorem first_root (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).A0 v) :
    let q : V := v 0 + (v 2 + v 1)
    let k : V := v 9 + v 10
    let ell : V := (v 6 * v 7) * (v 7 * k)
    let A : V := v 6 + (p 1 : V) * q
    (q * (q * q)) ∣ v 7 ∧ (v 0 * q) % (q - 1) = (v 2 * A) % (q - 1) ∧
      ∃ τ : V, τ * τ = 1 + ell * (ell + k) := by
  intro q k ell A
  let Q3 : V := q * (q * q)
  let qm : V := q - 1
  have h1q : 1 < q := by
    have h2 : 1 ≤ v 2 + v 1 := pos_iff_one_le.mp (add_pos (hv 2) (hv 1))
    have : 1 + 1 ≤ v 0 + (v 2 + v 1) := add_le_add (pos_iff_one_le.mp (hv 0)) h2
    exact lt_of_lt_of_le (by simp) this
  have hqm : 0 < qm := tsub_pos_of_lt h1q
  have hq0 : 0 < q := lt_trans (by simp) h1q
  have hQ3 : 0 < Q3 := mul_pos hq0 (mul_pos hq0 hq0)
  let M0 : V := Q3 * qm
  have hM0 : 0 < M0 := mul_pos hQ3 hqm
  let P : V := M0 * (ell + v 8) + v 7 * qm + (v 0 * q) * Q3
  let N : V := (v 2 * A) * Q3
  rw [internalZero_iff, A0_eval] at hz
  have hqmι : ι qm = ι q - 1 := by
    simpa using ι_tsub (V := V) (le_of_lt h1q)
  have hqι : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q = ι q := by
    simp only [vals, q, map_add]
  have hZ : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Z = ι P - ι N := by
    simp only [vals, P, N, M0, Q3, A, ell, k, map_add, map_mul, cast_port]
    rw [hqmι]
    simp only [q, map_add]
    ring
  have hM0ι : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).M0 = ι M0 := by
    simp only [vals, M0, Q3, map_mul]
    rw [hqmι]
    simp only [q, map_add]
  have hellι : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).ell = ι ell := by
    simp only [vals, ell, k, map_add, map_mul]
  have hkι : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k = ι k := by
    simp only [vals, k, map_add]
  rw [hZ, hM0ι, hellι, hkι] at hz
  have hmag : magnitude (P, N) * magnitude (P, N) = M0 * M0 * (1 + ell * (ell + k)) := by
    apply ι_injective
    rw [map_mul, ι_magnitude_sq]
    simp only [map_mul, map_add, map_one]
    linear_combination hz
  obtain ⟨τ, hτ, hττ⟩ := scaled_quotient M0 _ _ hM0 hmag
  have hmod : P % M0 = N % M0 :=
    ArithmeticAdaptiveFirstDivisibility2011.magnitude_mod (P, N) M0 hM0 ⟨τ, hτ⟩
  have hdQ : Q3 ∣ M0 := ⟨qm, rfl⟩
  have hP3 : P % Q3 = N % Q3 := by
    have h : P % M0 % Q3 = N % M0 % Q3 := congrArg (fun x : V => x % Q3) hmod
    rwa [ArithmeticAdaptiveFirstDivisibility2011.mod_mod_dvd hQ3 hdQ,
      ArithmeticAdaptiveFirstDivisibility2011.mod_mod_dvd hQ3 hdQ] at h
  have eP : P = v 7 * qm + Q3 * (qm * (ell + v 8) + v 0 * q) := by
    simp only [P, M0]; ring
  have eN : N = 0 + Q3 * (v 2 * A) := by simp only [N]; ring
  rw [eP, eN, mod_add_mul' _ _ hQ3, mod_add_mul' _ _ hQ3] at hP3
  have hdvd : Q3 ∣ qm * v 7 := by
    apply mod_eq_zero_iff_dvd.mp
    rw [mul_comm]
    simpa using hP3
  have hqq : q = qm + 1 := (tsub_add_cancel_of_le (le_of_lt h1q)).symm
  have hunit : ArithmeticGcdNormalization.Bez qm Q3 1 := by
    refine ⟨q * q + q + 1, 0, 0, 1, ?_⟩
    simp only [Q3]
    rw [hqq]
    ring
  have hY : Q3 ∣ v 7 := ArithmeticGcdNormalization.unit_certificate_cancel hunit hdvd
  obtain ⟨s, hs⟩ := hY
  have eP2 : P = Q3 * (qm * (ell + v 8 + s) + v 0 * q) := by
    simp only [P, M0]; rw [hs]; ring
  have eN2 : N = Q3 * (v 2 * A) := by simp only [N]; ring
  rw [eP2, eN2, show M0 = Q3 * qm from rfl,
    ArithmeticModularCancellation.mul_mod_mul hQ3 hqm,
    ArithmeticModularCancellation.mul_mod_mul hQ3 hqm] at hmod
  have hc := mul_left_cancel₀ (ne_of_gt hQ3) hmod
  rw [add_comm, mod_add_mul' _ _ hqm] at hc
  exact ⟨⟨s, hs⟩, hc, τ, hττ⟩

end P72Root

#print axioms P72Root.strong_root
#print axioms P72Root.first_root
