import GowersSzemeredi.Proofs05QuadraticPhaseError
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition

/-! Transfer the already audited upstream Schmidt recurrence theorem to the
centered modular norm used in Gowers's Section 16. For each fixed degree,
the exponent is quadratic in the number of simultaneous coefficients.
Combining degrees 1 through k gives exponent p*(d+1)^(2*k), with one
common multiplier for all d coefficient families. The degree constants are
existential. Proofs05SimultaneousMultiaffinePartition and
Proofs16SimultaneousRecurrence use these inputs to construct proper box
partitions; the final all-length threshold remains a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem centered_monomial_of_integer_approximation {N q k : Nat} [NeZero N]
    (a : ZMod N) (b : Int) {R : Real}
    (h : |(q : Real) ^ k * ((a.valMinAbs : Real) / N) - b| < R) :
    (centeredAbs ((q : ZMod N) ^ k * a) : Real) < R * N := by
  let E : Int := (q : Int) ^ k * a.valMinAbs - b * N
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcast : (E : ZMod N) = (q : ZMod N) ^ k * a := by
    simp [E, ZMod.coe_valMinAbs]
  have hE : (E : Real) = N * ((q : Real) ^ k * ((a.valMinAbs : Real) / N) - b) := by
    dsimp [E]
    push_cast
    field_simp
  have hcenter : (centeredAbs (E : ZMod N) : Real) ≤ (E.natAbs : Real) := by
    exact_mod_cast recurrence_centeredAbs_intCast_le (N := N) E
  rw [hcast] at hcenter
  calc
    _ ≤ (E.natAbs : Real) := hcenter
    _ = |(E : Real)| := by simp
    _ = N * |(q : Real) ^ k * ((a.valMinAbs : Real) / N) - b| := by
      rw [hE, abs_mul, abs_of_pos hN]
    _ < N * R := mul_lt_mul_of_pos_left h hN
    _ = R * N := mul_comm _ _

/-- A fixed degree admits polynomial dependence on the number of modular
coefficients. The constants are existential and do not give a box partition. -/
theorem simultaneous_modular_monomial_recurrence (j : Nat) :
    ∃ (K : Real) (p : Nat), 1 ≤ K ∧ 0 < p ∧
      ∀ (N : Nat) [NeZero N] (ι : Type) [Fintype ι]
        (a : ι → ZMod N) (M : Nat) (R : Real), 0 < R → R ≤ 1 →
        (K * ((Fintype.card ι : Real) + 1) / R) ^
          (p * (Fintype.card ι + 1) ^ 2) ≤ M →
        ∃ q : Nat, 0 < q ∧ q ≤ M ∧ ∀ i,
          (centeredAbs ((q : ZMod N) ^ (j + 1) * a i) : Real) < R * N := by
  obtain ⟨K, p, hK, hp, hrec⟩ := OAI.Erdos3.simultaneous_monomial_recurrence j
  refine ⟨K, p, hK, hp, ?_⟩
  intro N _ ι _ a M R hR hR1 hM
  obtain ⟨q, hq, hqM, b, hb⟩ :=
    hrec ι (fun i => (a i).valMinAbs / (N : Real)) M R hR hR1 hM
  exact ⟨q, hq, hqM, fun i => centered_monomial_of_integer_approximation (a i) (b i) (hb i)⟩


/-- A fixed number of degrees preserves polynomial dependence on family size. -/
theorem schmidt_mixed_exponent_bound (p e d k : Nat) :
    (2 + (k + 1) * (p * (d + 1) ^ (2 * k))) * (e * (d + 1) ^ 2) +
        p * (d + 1) ^ (2 * k) ≤
      (p + e * (2 + (k + 1) * p)) * (d + 1) ^ (2 * (k + 1)) := by
  have h1 : 1 ≤ (d + 1) ^ (2 * k) := one_le_pow₀ (by omega)
  have h2 : 1 ≤ (d + 1) ^ 2 := one_le_pow₀ (by omega)
  have ha := Nat.mul_le_mul_left (2 * e * (d + 1) ^ 2) h1
  have hb := Nat.mul_le_mul_left (p * (d + 1) ^ (2 * k)) h2
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
  nlinarith only [ha, hb]

/-- At resolution H, one multiplier makes every monomial in d families
and degrees 1 through k smaller than N/H in centered modular norm. -/
def MixedModularRecurrenceBound (k : Nat) (K : Real) (p : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (d H : Nat), 0 < H →
    K * ((d : Real) + 1) ≤ H → ∀ a : Fin d → Fin k → ZMod N,
      ∃ q : Nat, 0 < q ∧ q ≤ H ^ (p * (d + 1) ^ (2 * k)) ∧ ∀ i j,
        (centeredAbs ((q : ZMod N) ^ (j.val + 1) * a i j) : Real) * H < N

/-- Simultaneous recurrence for all degrees up to k. The fixed-degree
constants do not depend on the modulus, family size, or resolution. -/
theorem exists_mixed_modular_recurrence_bound (k : Nat) :
    ∃ (K : Real) (p : Nat), 1 ≤ K ∧ 0 < p ∧ MixedModularRecurrenceBound k K p := by
  induction k with
  | zero =>
      refine ⟨1, 1, le_rfl, by decide, ?_⟩
      intro N _ d H hH _ a
      refine ⟨1, by decide, ?_, fun _ j => Fin.elim0 j⟩
      simpa using (show 1 ≤ H by omega)
  | succ k ih =>
      obtain ⟨K, p, hK, hp, hrec⟩ := ih
      obtain ⟨L, e, hL, he, hmono⟩ := simultaneous_modular_monomial_recurrence k
      refine ⟨max K L, p + e * (2 + (k + 1) * p), hK.trans (le_max_left _ _), by omega, ?_⟩
      intro N _ d H hH hscale a
      have hd : (0 : Real) ≤ (d : Real) + 1 := by positivity
      have hKH : K * ((d : Real) + 1) ≤ H :=
        (mul_le_mul_of_nonneg_right (le_max_left K L) hd).trans hscale
      have hLH : L * ((d : Real) + 1) ≤ H :=
        (mul_le_mul_of_nonneg_right (le_max_right K L) hd).trans hscale
      let A := p * (d + 1) ^ (2 * k)
      let Q := H ^ A
      let B := (2 + (k + 1) * A) * (e * (d + 1) ^ 2)
      let R : Real := ((H : Real) * (Q : Real) ^ (k + 1))⁻¹
      have hHr : (0 : Real) < H := by exact_mod_cast hH
      have hQ : 0 < Q := pow_pos hH _
      have hQr : (0 : Real) < Q := by exact_mod_cast hQ
      have hden : (0 : Real) < H * (Q : Real) ^ (k + 1) := mul_pos hHr (pow_pos hQr _)
      have hden1 : (1 : Real) ≤ H * (Q : Real) ^ (k + 1) := by
        exact_mod_cast (show 1 ≤ H * Q ^ (k + 1) by
          have := Nat.mul_pos hH (pow_pos hQ (k + 1))
          omega)
      have hR : 0 < R := inv_pos.mpr hden
      have hR1 : R ≤ 1 := by
        simpa [R] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hden1
      have hbase : L * ((d : Real) + 1) / R ≤ (H : Real) ^ (2 + (k + 1) * A) := by
        calc
          _ = (L * ((d : Real) + 1)) * (H * (Q : Real) ^ (k + 1)) := by simp only [R, div_inv_eq_mul]
          _ ≤ H * (H * (Q : Real) ^ (k + 1)) := mul_le_mul_of_nonneg_right hLH hden.le
          _ = (H : Real) ^ (2 + (k + 1) * A) := by
            simp only [Q, Nat.cast_pow, pow_add, pow_mul]
            ring
      have hsearch : (L * ((Fintype.card (Fin d) : Real) + 1) / R) ^
          (e * (Fintype.card (Fin d) + 1) ^ 2) ≤ (H ^ B : Nat) := by
        simp only [Fintype.card_fin, Nat.cast_pow]
        exact (pow_le_pow_left₀ (by positivity) hbase _).trans_eq (by rw [← pow_mul])
      obtain ⟨q1, hq1, hq1B, hq1small⟩ := hmono N (Fin d) (fun i => a i (Fin.last k))
        (H ^ B) R hR hR1 hsearch
      obtain ⟨q2, hq2, hq2Q, hq2small⟩ := hrec N d H hH hKH
        (fun i j => (q1 : ZMod N) ^ (j.val + 1) * a i j.castSucc)
      refine ⟨q1 * q2, Nat.mul_pos hq1 hq2, ?_, ?_⟩
      · calc
          q1 * q2 ≤ H ^ B * H ^ A := Nat.mul_le_mul hq1B hq2Q
          _ = H ^ (B + A) := (pow_add _ _ _).symm
          _ ≤ H ^ ((p + e * (2 + (k + 1) * p)) * (d + 1) ^ (2 * (k + 1))) :=
            Nat.pow_le_pow_right hH (schmidt_mixed_exponent_bound p e d k)
      · intro i j
        refine Fin.lastCases ?_ (fun t => ?_) j
        · have hid : ((q1 * q2 : Nat) : ZMod N) ^ (k + 1) * a i (Fin.last k) =
              ((q1 : ZMod N) ^ (k + 1) * a i (Fin.last k)) * (q2 : ZMod N) ^ (k + 1) := by
            push_cast
            ring
          have hsmall : (centeredAbs ((q1 : ZMod N) ^ (k + 1) * a i (Fin.last k)) : Real) *
              (H * (Q : Real) ^ (k + 1)) < N := by
            apply (lt_div_iff₀ hden).mp
            simpa [R, div_eq_mul_inv, mul_comm] using hq1small i
          have hmul : (centeredAbs (((q1 : ZMod N) ^ (k + 1) * a i (Fin.last k)) *
                (q2 : ZMod N) ^ (k + 1)) : Real) ≤
              (centeredAbs ((q1 : ZMod N) ^ (k + 1) * a i (Fin.last k)) : Real) * (q2 : Real) ^ (k + 1) := by
            exact_mod_cast centeredAbs_mul_natCast_pow_le ((q1 : ZMod N) ^ (k + 1) * a i (Fin.last k)) q2 (k + 1)
          change (centeredAbs (((q1 * q2 : Nat) : ZMod N) ^ (k + 1) * a i (Fin.last k)) : Real) * H < N
          rw [hid]
          apply lt_of_le_of_lt _ hsmall
          calc
            _ ≤ ((centeredAbs ((q1 : ZMod N) ^ (k + 1) * a i (Fin.last k)) : Real) *
                  (q2 : Real) ^ (k + 1)) * H := mul_le_mul_of_nonneg_right hmul hHr.le
            _ ≤ ((centeredAbs ((q1 : ZMod N) ^ (k + 1) * a i (Fin.last k)) : Real) *
                  (Q : Real) ^ (k + 1)) * H := by
              gcongr
            _ = _ := by ring
        · have hid : ((q1 * q2 : Nat) : ZMod N) ^ (t.val + 1) * a i t.castSucc =
              (q2 : ZMod N) ^ (t.val + 1) * ((q1 : ZMod N) ^ (t.val + 1) * a i t.castSucc) := by
            push_cast
            ring
          change (centeredAbs (((q1 * q2 : Nat) : ZMod N) ^ (t.val + 1) * a i t.castSucc) : Real) * H < N
          rw [hid]
          exact hq2small i t

/-- One pair of constants works for every degree from 1 through k.
The recurrence step may depend on the chosen degree. -/
def UniformModularMonomialRecurrence (k : Nat) (K : Real) (p : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (ι : Type) [Fintype ι]
    (a : ι → ZMod N) (M : Nat) (R : Real), 0 < R → R ≤ 1 →
    (K * ((Fintype.card ι : Real) + 1) / R) ^
      (p * (Fintype.card ι + 1) ^ 2) ≤ M →
    ∀ j : Fin k, ∃ q : Nat, 0 < q ∧ q ≤ M ∧ ∀ i,
      (centeredAbs ((q : ZMod N) ^ (j.val + 1) * a i) : Real) < R * N

/-- Uniformize the degree-dependent Schmidt constants over a finite range. -/
theorem exists_uniform_modular_monomial_recurrence (k : Nat) :
    ∃ (K : Real) (p : Nat), 1 ≤ K ∧ 0 < p ∧ UniformModularMonomialRecurrence k K p := by
  classical
  choose K p hK hp hrec using (fun j : Fin k => simultaneous_modular_monomial_recurrence j.val)
  let C : Real := 1 + ∑ j : Fin k, K j
  let e : Nat := 1 + ∑ j : Fin k, p j
  have hK0 (j : Fin k) : 0 ≤ K j := (by norm_num : (0 : Real) ≤ 1).trans (hK j)
  have hC : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hK0 j))
  have he : 0 < e := by dsimp [e]; omega
  have hKC (j : Fin k) : K j ≤ C := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hK0 i) (Finset.mem_univ j)
    dsimp [C]
    linarith
  have hpe (j : Fin k) : p j ≤ e := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => Nat.zero_le (p i)) (Finset.mem_univ j)
    dsimp [e]
    omega
  refine ⟨C, e, hC, he, ?_⟩
  intro N _ ι _ a M R hR hR1 hM j
  apply hrec j N ι a M R hR hR1
  have hc : (1 : Real) ≤ (Fintype.card ι : Real) + 1 := by norm_num
  have hbase : 1 ≤ C * ((Fintype.card ι : Real) + 1) / R := by
    rw [le_div_iff₀ hR, one_mul]
    exact hR1.trans ((by simpa using mul_le_mul hC hc (by norm_num : (0 : Real) ≤ 1) (by linarith : 0 ≤ C)))
  have hKj : 0 ≤ K j := hK0 j
  calc
    _ ≤ (C * ((Fintype.card ι : Real) + 1) / R) ^ (p j * (Fintype.card ι + 1) ^ 2) :=
      pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hKC j) (by positivity)) hR.le) _
    _ ≤ (C * ((Fintype.card ι : Real) + 1) / R) ^ (e * (Fintype.card ι + 1) ^ 2) :=
      pow_le_pow_right₀ hbase (Nat.mul_le_mul_right _ (hpe j))
    _ ≤ M := hM

end LeanProofs.GowersSzemeredi
