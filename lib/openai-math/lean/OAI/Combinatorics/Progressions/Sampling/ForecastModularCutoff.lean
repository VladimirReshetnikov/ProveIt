import OAI.Combinatorics.Progressions.Lattices.RationalForecastResidueMass

namespace OAI

section

namespace Erdos3

theorem forecastJointGridPrefactor_le_exp (dout dj dc d : ℕ)
    (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {P E T D L C K : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hT : 1 ≤ T) (hTexp : T ≤ Real.exp (P + E + 5))
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDexp : D ≤ Real.exp P) (hLexp : L ≤ Real.exp P)
    (hCexp : C ≤ Real.exp P) (hKexp : K ≤ Real.exp P) :
    (T ^ (dout + 1) * (2 * 8 ^ dj * (L + C * K)) +
      (D / T) * (8 ^ dj * L)) * 6 ^ dc ≤
      Real.exp (((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 4) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h6 : (6 : ℝ) ≤ Real.exp 3 := (by norm_num : (6 : ℝ) ≤ 8).trans h8
  have hR : 0 ≤ P + E + 5 := by linarith
  have hdoutR : (dout : ℝ) ≤ d := by exact_mod_cast hdout
  have hdjR : (dj : ℝ) ≤ d := by exact_mod_cast hdj
  have hdcR : (dc : ℝ) ≤ d := by exact_mod_cast hdc
  have hTp : T ^ (dout + 1) ≤ Real.exp (((d : ℝ) + 1) * (P + E + 5)) := by
    calc
      _ ≤ (Real.exp (P + E + 5)) ^ (dout + 1) :=
        pow_le_pow_left₀ (by linarith) hTexp _
      _ = Real.exp (((dout : ℝ) + 1) * (P + E + 5)) := by
        rw [← Real.exp_nat_mul]
        simp
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hR)
  have hjp : (8 : ℝ) ^ dj ≤ Real.exp (3 * (d : ℝ)) := by
    calc
      _ ≤ (Real.exp 3) ^ dj := pow_le_pow_left₀ (by norm_num) h8 _
      _ = Real.exp ((dj : ℝ) * 3) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcp : (6 : ℝ) ^ dc ≤ Real.exp (3 * (d : ℝ)) := by
    calc
      _ ≤ (Real.exp 3) ^ dc := pow_le_pow_left₀ (by norm_num) h6 _
      _ = Real.exp ((dc : ℝ) * 3) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsum : L + C * K ≤ Real.exp (2 * P + 1) := by
    have hCK : C * K ≤ Real.exp (2 * P) := by
      calc
        _ ≤ Real.exp P * Real.exp P := mul_le_mul hCexp hKexp hK (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hL2 := hLexp.trans (Real.exp_le_exp.mpr (show P ≤ 2 * P by linarith))
    calc
      _ ≤ 2 * Real.exp (2 * P) := by linarith
      _ ≤ Real.exp 1 * Real.exp (2 * P) := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hDT : D / T ≤ Real.exp P :=
    (div_le_self hD hT).trans hDexp
  let H := ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 2
  have hfirst : T ^ (dout + 1) * (2 * 8 ^ dj * (L + C * K)) * 6 ^ dc ≤
      Real.exp H := by
    calc
      _ ≤ Real.exp (((d : ℝ) + 1) * (P + E + 5)) *
          (Real.exp 1 * Real.exp (3 * d) * Real.exp (2 * P + 1)) * Real.exp (3 * d) := by
        gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; dsimp [H]; ring
  have hsecond : (D / T) * (8 ^ dj * L) * 6 ^ dc ≤ Real.exp H := by
    calc
      _ ≤ Real.exp P * (Real.exp (3 * d) * Real.exp P) * Real.exp (3 * d) := by
        gcongr
      _ = Real.exp (6 * (d : ℝ) + 2 * P) := by
        simp only [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hp : 0 ≤ ((d : ℝ) + 1) * (P + E + 5) := mul_nonneg (by positivity) hR
        dsimp [H]
        linarith)
  rw [add_mul]
  calc
    _ ≤ 2 * Real.exp H := by linarith
    _ ≤ Real.exp 1 * Real.exp H := mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
    _ = Real.exp (H + 1) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [H]; linarith)

end Erdos3

end

section

namespace Erdos3

theorem exists_rationalForecast_order_cutoff {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    ∃ T : ℕ, 0 < T ∧ (T : ℝ) ≤ Real.exp (P + E + 2) ∧
      ∀ C : ℝ, C ≤ Real.exp P → C / T ≤ Real.exp (-E) := by
  let T := ⌈Real.exp (P + E)⌉₊
  have hlow : Real.exp (P + E) ≤ (T : ℝ) := Nat.le_ceil _
  have hT : 0 < T := by exact_mod_cast (Real.exp_pos (P + E)).trans_le hlow
  have hupp : (T : ℝ) ≤ Real.exp (P + E) + 1 := (Nat.ceil_lt_add_one
    (Real.exp_nonneg (P + E))).le
  have hbase : 1 ≤ Real.exp (P + E) := Real.one_le_exp (by linarith)
  have hexp2 : 2 ≤ Real.exp (2 : ℝ) := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨T, hT, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (P + E) + 1 := hupp
      _ ≤ Real.exp (P + E) * Real.exp 2 := by nlinarith
      _ = _ := (Real.exp_add _ _).symm
  · intro C hC
    apply (div_le_iff₀ (by exact_mod_cast hT : (0 : ℝ) < T)).mpr
    calc
      _ ≤ Real.exp P := hC
      _ = Real.exp (-E) * Real.exp (P + E) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_nonneg _)

theorem rationalForecast_cutoff_power_bound {P E : ℝ} {T : ℕ}
    (hT : (T : ℝ) ≤ Real.exp (P + E + 2)) (d : ℕ) :
    (T : ℝ) ^ d ≤ Real.exp ((d : ℝ) * (P + E + 2)) := by
  calc
    _ ≤ (Real.exp (P + E + 2)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg T) hT d
    _ = _ := by rw [← Real.exp_nat_mul]

end Erdos3

end

section

namespace Erdos3

theorem exists_forecast_approximation_parameters (d : ℕ)
    {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    ∃ (T : ℕ) (ε : ℝ),
      0 < T ∧ (T : ℝ) ≤ Real.exp (P + E + 3) ∧
      0 < ε ∧ ε ≤ 1 ∧
      ε⁻¹ ≤ Real.exp (E + 1 + d * (P + E + 3)) ∧
      ∀ C : ℝ, C ≤ Real.exp P →
        C / T + (T : ℝ) ^ d * ε ≤ Real.exp (-E) := by
  obtain ⟨T, hT, hTbound, htail⟩ := exists_rationalForecast_order_cutoff hP
    (show 0 ≤ E + 1 by linarith)
  have hTbound' : (T : ℝ) ≤ Real.exp (P + E + 3) := by
    convert hTbound using 1
    congr 1
    ring
  let Q := E + 1 + d * (P + E + 3)
  let ε := Real.exp (-Q)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hQ)
  have hεinv : ε⁻¹ ≤ Real.exp Q := by
    dsimp only [ε]
    rw [← Real.exp_neg, neg_neg]
  have hcount : (T : ℝ) ^ d * ε ≤ Real.exp (-(E + 1)) := by
    calc
      _ ≤ (Real.exp (P + E + 3)) ^ d * ε :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hTbound' d) hε.le
      _ = Real.exp (-(E + 1)) := by
        rw [← Real.exp_nat_mul]
        dsimp only [ε, Q]
        rw [← Real.exp_add]
        congr 1
        ring
  refine ⟨T, ε, hT, hTbound', hε, hε1, hεinv, ?_⟩
  intro C hC
  calc
    _ ≤ Real.exp (-(E + 1)) + Real.exp (-(E + 1)) := add_le_add (htail C hC) hcount
    _ = 2 * Real.exp (-(E + 1)) := (two_mul _).symm
    _ ≤ Real.exp 1 * Real.exp (-(E + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)])
        (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

theorem exists_forecast_weighted_approximation_parameters (d : ℕ)
    {Psm Pin Pdec E : ℝ} (hPsm : 0 ≤ Psm) (hPin : 0 ≤ Pin)
    (hPdec : 0 ≤ Pdec) (hE : 0 ≤ E) :
    ∃ (T : ℕ) (ε : ℝ),
      0 < T ∧ (T : ℝ) ≤ Real.exp (Pin + Pdec + (E + Psm) + 3) ∧
      0 < ε ∧ ε ≤ 1 ∧
      ε⁻¹ ≤ Real.exp (E + Psm + 1 + d * (Pin + Pdec + (E + Psm) + 3)) ∧
      ∀ H I C : ℝ, 0 ≤ H → 0 ≤ C → H ≤ Real.exp Psm → I ≤ Real.exp Pin →
        C ≤ Real.exp Pdec →
        H * (I * (C / T) + (T : ℝ) ^ d * ε) ≤ Real.exp (-E) := by
  obtain ⟨T, ε, hT, hTbound, hε, hε1, hεinv, herr⟩ :=
    exists_forecast_approximation_parameters d (add_nonneg hPin hPdec) (add_nonneg hE hPsm)
  refine ⟨T, ε, hT, hTbound, hε, hε1, hεinv, ?_⟩
  intro H I C hH hC hHcap hIcap hCcap
  have hIC : I * C ≤ Real.exp (Pin + Pdec) := by
    rw [Real.exp_add]
    exact mul_le_mul hIcap hCcap hC (Real.exp_nonneg _)
  have herror := herr (I * C) hIC
  rw [mul_div_assoc] at herror
  calc
    _ ≤ H * Real.exp (-(E + Psm)) := mul_le_mul_of_nonneg_left herror hH
    _ ≤ Real.exp Psm * Real.exp (-(E + Psm)) :=
      mul_le_mul_of_nonneg_right hHcap (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

noncomputable def forecastJointGridCutoff (P E : ℝ) : ℕ :=
  ⌈Real.exp (P + E + 4)⌉₊

theorem forecastJointGridCutoff_lower (P E : ℝ) :
    Real.exp (P + E + 4) ≤ (forecastJointGridCutoff P E : ℝ) := Nat.le_ceil _

theorem forecastJointGridCutoff_pos_unconditional (P E : ℝ) : 0 < forecastJointGridCutoff P E := by
  exact_mod_cast (Real.exp_pos (P + E + 4)).trans_le (forecastJointGridCutoff_lower P E)

theorem forecastJointGridCutoff_one_le (P E : ℝ) : 1 ≤ forecastJointGridCutoff P E :=
  forecastJointGridCutoff_pos_unconditional P E

theorem forecastJointGridCutoff_pos {P E : ℝ} (_hP : 0 ≤ P) (_hE : 0 ≤ E) :
    0 < forecastJointGridCutoff P E := forecastJointGridCutoff_pos_unconditional P E

theorem forecastJointGridCutoff_le_exp {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    (forecastJointGridCutoff P E : ℝ) ≤ Real.exp (P + E + 5) := by
  calc
    _ ≤ Real.exp (P + E + 4) + 1 := (Nat.ceil_lt_add_one (Real.exp_nonneg _)).le
    _ = 1 + Real.exp (P + E + 4) := add_comm _ _
    _ ≤ Real.exp ((P + E + 4) + 1) :=
      one_add_le_exp_succ (by linarith) le_rfl
    _ = _ := by congr 1; ring

theorem forecastJointGridCutoff_div_bound {P E D : ℝ} (hD : D ≤ Real.exp P) :
    D / forecastJointGridCutoff P E ≤ Real.exp (-(E + 4)) := by
  have hpos : (0 : ℝ) < forecastJointGridCutoff P E := by
    exact_mod_cast forecastJointGridCutoff_pos_unconditional P E
  apply (div_le_iff₀ hpos).mpr
  calc
    D ≤ Real.exp P := hD
    _ = Real.exp (-(E + 4)) * Real.exp (P + E + 4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (forecastJointGridCutoff_lower P E) (Real.exp_nonneg _)

theorem forecastJointGridCutoff_tail_le {P E D : ℝ} (_hP : 0 ≤ P) (_hE : 0 ≤ E)
    (hD : D ≤ Real.exp P) :
    D / forecastJointGridCutoff P E ≤ Real.exp (-(E + 4)) :=
  forecastJointGridCutoff_div_bound hD

end Erdos3

end

section

namespace Erdos3

theorem exists_forecast_mesh_floor {P V E : ℝ}
    (hP : 0 ≤ P) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    ∃ Lmin : ℕ, 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (P + V + E + 2) ∧
      ∀ {K : ℝ} {q S : ℕ}, 0 ≤ K → K ≤ Real.exp P →
        (q : ℝ) ≤ Real.exp V → Lmin ≤ S →
        K * ((q : ℝ) / S) ≤ Real.exp (-E) := by
  obtain ⟨Lmin, hL, hbound, herror⟩ :=
    exists_rationalForecast_order_cutoff (add_nonneg hP hV) hE
  refine ⟨Lmin, hL, hbound, ?_⟩
  intro K q S hK hKP hq hS
  have hKq : K * (q : ℝ) ≤ Real.exp (P + V) := by
    rw [Real.exp_add]
    exact mul_le_mul hKP hq (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hsmall := herror (K * q) hKq
  have hLr : (0 : ℝ) < Lmin := by exact_mod_cast hL
  have hSr : (Lmin : ℝ) ≤ S := by exact_mod_cast hS
  calc
    _ = (K * q) / S := (mul_div_assoc _ _ _).symm
    _ ≤ (K * q) / Lmin := div_le_div_of_nonneg_left (by positivity) hLr hSr
    _ ≤ _ := hsmall

theorem exists_active_residue_mesh_floor {D V E : ℝ}
    (hD : 0 ≤ D) (hV : 0 ≤ V) (hE : 0 ≤ E) :
    ∃ Lmin : ℕ, 0 < Lmin ∧ (Lmin : ℝ) ≤ Real.exp (D + V + E + 4) ∧
      ∀ {d q S : ℕ}, (d : ℝ) ≤ Real.exp D → (q : ℝ) ≤ Real.exp V → Lmin ≤ S →
        4 * d * ((q : ℝ) / S) ≤ Real.exp (-E) := by
  obtain ⟨Lmin, hL, hbound, herror⟩ := exists_forecast_mesh_floor
    (show 0 ≤ D + 2 by linarith) hV hE
  refine ⟨Lmin, hL, ?_, ?_⟩
  · convert hbound using 1
    congr 1
    ring
  · intro d q S hd hq hS
    apply herror (by positivity) _ hq hS
    have hfour : (4 : ℝ) ≤ Real.exp 2 := by
      have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at h
      linarith
    rw [Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 4 by norm_num),
      mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg D)]

end Erdos3

end

section

namespace Erdos3

def modularForecastRankConstant (s D : ℕ) : ℕ :=
  (D + 2) * (2 ^ s * s.factorial) * 2 ^ s

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem modularForecastRankConstant_dimension (s D d : ℕ) (hd : d ≤ D) :
    ((d + 2 : ℕ) : ℝ) ≤ modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) := by
  rw [modularForecastRankConstant_decay]
  exact_mod_cast Nat.add_le_add_right hd 2

end Erdos3

end

section

namespace Erdos3

noncomputable def forecastJointGridError
    (dout dj dc cutoff : ℕ) (D L C K δ : ℝ) : ℝ :=
  (((cutoff : ℝ) ^ (dout + 1) * (2 * (8 : ℝ) ^ dj * (L + C * K) * δ) +
    (D / cutoff) * ((8 : ℝ) ^ dj * L * δ)) * (6 : ℝ) ^ dc) + 2 * (D / cutoff)

noncomputable def forecastJointGridMeshLog (d : ℕ) (P E : ℝ) : ℝ :=
  ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + E + 8

noncomputable def forecastJointGridMesh (d : ℕ) (P E : ℝ) : ℝ :=
  Real.exp (-forecastJointGridMeshLog d P E)

theorem forecastJointGridMeshLog_nonneg (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) : 0 ≤ forecastJointGridMeshLog d P E := by
  unfold forecastJointGridMeshLog
  positivity

theorem forecastJointGridMesh_bounds (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 < forecastJointGridMesh d P E ∧ forecastJointGridMesh d P E ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (forecastJointGridMeshLog_nonneg d hP hE))⟩

theorem forecastJointGridError_absorb
    (dout dj dc d cutoff : ℕ) (hdout : dout ≤ d) (hdj : dj ≤ d) (hdc : dc ≤ d)
    {P E D L C K δ : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hcutoff : 1 ≤ cutoff) (hTexp : (cutoff : ℝ) ≤ Real.exp (P + E + 5))
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hDexp : D ≤ Real.exp P) (hLexp : L ≤ Real.exp P)
    (hCexp : C ≤ Real.exp P) (hKexp : K ≤ Real.exp P)
    (htail : D / cutoff ≤ Real.exp (-(E + 4)))
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ forecastJointGridMesh d P E) :
    forecastJointGridError dout dj dc cutoff D L C K δ ≤ Real.exp (-E) := by
  have hpref := forecastJointGridPrefactor_le_exp dout dj dc d hdout hdj hdc
    hP hE (by exact_mod_cast hcutoff) hTexp hD hL hC hK hDexp hLexp hCexp hKexp
  let H := ((d : ℝ) + 1) * (P + E + 5) + 6 * d + 2 * P + 4
  have hmesh : Real.exp H * δ ≤ Real.exp (-(E + 4)) := by
    calc
      _ ≤ Real.exp H * forecastJointGridMesh d P E :=
        mul_le_mul_of_nonneg_left hδsmall (Real.exp_nonneg _)
      _ = _ := by
        unfold forecastJointGridMesh forecastJointGridMeshLog H
        rw [← Real.exp_add]
        congr 1
        ring
  have hpre : forecastJointGridError dout dj dc cutoff D L C K δ ≤
      Real.exp H * δ + 2 * (D / cutoff) := by
    have hh := mul_le_mul_of_nonneg_right hpref hδ
    unfold forecastJointGridError
    dsimp only [H]
    nlinarith only [hh]
  have htotal : forecastJointGridError dout dj dc cutoff D L C K δ ≤
      3 * Real.exp (-(E + 4)) := by linarith only [hpre, hmesh, htail]
  have hthree : (3 : ℝ) ≤ Real.exp 4 := by linarith only [Real.add_one_le_exp (4 : ℝ)]
  refine htotal.trans ?_
  calc
    _ ≤ Real.exp 4 * Real.exp (-(E + 4)) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem forecastJointGridErrorBudget (d : ℕ) {P E : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) :
    1 ≤ forecastJointGridCutoff P E ∧
    (forecastJointGridCutoff P E : ℝ) ≤ Real.exp (P + E + 5) ∧
    0 < forecastJointGridMesh d P E ∧ forecastJointGridMesh d P E ≤ 1 ∧
    ∀ {dout dj dc : ℕ}, dout ≤ d → dj ≤ d → dc ≤ d →
    ∀ {D L C K δ : ℝ}, 0 ≤ D → 0 ≤ L → 0 ≤ C → 0 ≤ K →
    D ≤ Real.exp P → L ≤ Real.exp P → C ≤ Real.exp P → K ≤ Real.exp P →
    0 ≤ δ → δ ≤ forecastJointGridMesh d P E →
    forecastJointGridError dout dj dc (forecastJointGridCutoff P E) D L C K δ ≤
      Real.exp (-E) := by
  have hm := forecastJointGridMesh_bounds d hP hE
  refine ⟨forecastJointGridCutoff_one_le P E, forecastJointGridCutoff_le_exp hP hE,
    hm.1, hm.2, ?_⟩
  intro dout dj dc hdout hdj hdc D L C K δ hD hL hC hK hDexp hLexp hCexp hKexp hδ hδsmall
  exact forecastJointGridError_absorb dout dj dc d (forecastJointGridCutoff P E)
    hdout hdj hdc hP hE (forecastJointGridCutoff_one_le P E)
    (forecastJointGridCutoff_le_exp hP hE) hD hL hC hK hDexp hLexp hCexp hKexp
    (forecastJointGridCutoff_tail_le hP hE hDexp) hδ hδsmall

end Erdos3

end

section

namespace Erdos3

theorem forecastModularCharge_exp_bound (m D Rbad Qpres : ℕ)
    {Pbad Ppres : ℝ} (hR : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hQ : (Qpres : ℝ) ≤ Real.exp Ppres) :
    ((Rbad * Qpres : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) *
        modularRankChargeFactor m) ≤
      Real.exp ((Pbad + Ppres) * ((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) := by
  rw [modularForecastRankConstant_decay]
  have hbase : ((Rbad * Qpres : ℕ) : ℝ) ≤ Real.exp (Pbad + Ppres) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hR hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ (Real.exp (Pbad + Ppres)) ^
        (((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hbase (by positivity)
    _ = _ := by rw [← Real.exp_mul, mul_assoc]

theorem exists_forecast_modular_approximation_parameters (m D d : ℕ)
    {Psm Pin Pbad Ppres E : ℝ}
    (hPsm : 0 ≤ Psm) (hPin : 0 ≤ Pin) (hPbad : 0 ≤ Pbad)
    (hPpres : 0 ≤ Ppres) (hE : 0 ≤ E) :
    let Pdec := (Pbad + Ppres) * ((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    ∃ (T : ℕ) (ε : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp V ∧
      0 < ε ∧ ε ≤ 1 ∧ ε⁻¹ ≤ Real.exp (E + Psm + 1 + d * V) ∧
      ∀ (Rbad Qpres : ℕ) (H I : ℝ),
        0 ≤ H → H ≤ Real.exp Psm → I ≤ Real.exp Pin →
        (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres →
        H * (I * ((((Rbad * Qpres : ℕ) : ℝ) ^
          (modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) *
            modularRankChargeFactor m)) / T) + (T : ℝ) ^ d * ε) ≤ Real.exp (-E) := by
  intro Pdec V
  have hPdec : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  obtain ⟨T, ε, hT, hTb, hε, hε1, hεb, herror⟩ :=
    exists_forecast_weighted_approximation_parameters d hPsm hPin hPdec hE
  refine ⟨T, ε, hT, hTb, hε, hε1, hεb, ?_⟩
  intro Rbad Qpres H I hH hHcap hIcap hR hQ
  exact herror H I _ hH (Real.rpow_nonneg (Nat.cast_nonneg _) _) hHcap hIcap
    (forecastModularCharge_exp_bound m D Rbad Qpres hR hQ)

end Erdos3

end

end OAI
