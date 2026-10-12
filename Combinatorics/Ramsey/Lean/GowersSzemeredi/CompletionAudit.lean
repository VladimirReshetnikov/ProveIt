import GowersSzemeredi.NumberedAudit
import GowersSzemeredi.Proofs18CoverSharperComparisons
import GowersSzemeredi.Proofs18CoverSharperAllDegrees
import GowersSzemeredi.Proofs18CoverFejerAllDegrees
import Lean.Util.CollectAxioms

/-! Production verification entry point: all numbered catalogue companions
and the stronger inverse, progression, and two-color bounds, including their
every-degree and every-length forms (Proofs18CoverSharperAllDegrees). -/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let strengthened : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_18_1_sharper_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_sharper_six_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d7_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L5_eleven_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_sharper_six_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L5_eleven_le,
    ``LeanProofs.GowersSzemeredi.section18ExponentAt_strictAnti,
    ``LeanProofs.GowersSzemeredi.szemerediThresholdAt_strictMono,
    ``LeanProofs.GowersSzemeredi.twoColorThresholdAt_strictMono
  ]
  for name in strengthened do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the nine improved-bound and comparison theorems; only approved axioms."

-- Exact statements of the every-degree and every-length strengthenings.
example : ∀ d, LeanProofs.GowersSzemeredi.Theorem181AtSharp 7 d :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d7
example : ∀ L, LeanProofs.GowersSzemeredi.Theorem182AtSharp 5 L :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L5
example : ∀ L, LeanProofs.GowersSzemeredi.Corollary187AtSharp 5 L :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L5
example : ∀ L, LeanProofs.GowersSzemeredi.Theorem182AtSharp 6 L :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L6
example : ∀ L, LeanProofs.GowersSzemeredi.Corollary187AtSharp 6 L :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L6
example : LeanProofs.GowersSzemeredi.theorem_18_1 :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d7_implies_printed
example : LeanProofs.GowersSzemeredi.theorem_18_2 :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L6_implies_printed
example : LeanProofs.GowersSzemeredi.corollary_18_7 :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L6_implies_printed
example : ∀ (k r : Nat), 2 ≤ r → ∀ N : Nat,
    LeanProofs.GowersSzemeredi.szemerediThresholdAt 5 (1 / (r : Real)) k ≤ N →
      ∀ color : Nat → Fin r, LeanProofs.GowersSzemeredi.HasMonochromaticAP N r color k :=
  fun k _ hr N hN color => LeanProofs.GowersSzemeredi.van_der_waerden_L5 k hr N hN color
example : LeanProofs.GowersSzemeredi.Theorem13At 5 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L5
example : ∀ k : Nat, 1 ≤ k → LeanProofs.GowersSzemeredi.PolyCoverAt k
    (LeanProofs.GowersSzemeredi.uCount (2 ^ (2 ^ LeanProofs.GowersSzemeredi.tightMuV k))
      (LeanProofs.GowersSzemeredi.uDeg68 k))
    (LeanProofs.GowersSzemeredi.uExp (2 ^ (2 ^ LeanProofs.GowersSzemeredi.tightMuV k))
      (LeanProofs.GowersSzemeredi.uDeg68 k)) :=
  fun _ hk => LeanProofs.GowersSzemeredi.theorem_16_2_polynomial hk
example : LeanProofs.GowersSzemeredi.theorem_16_2 :=
  LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_implies_printed
example : ∀ k : Nat, 2 ≤ k → ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (236 * 2 ^ k + k + 24)) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ f : ZMod N → Complex, LeanProofs.GowersSzemeredi.DiscValued f →
          ¬ LeanProofs.GowersSzemeredi.UniformOfDegree f alpha (k + 2) →
          ∃ P : LeanProofs.GowersSzemeredi.Box N (k + 1),
            ∃ mu : LeanProofs.GowersSzemeredi.Point N (k + 1) → ZMod N,
              LeanProofs.GowersSzemeredi.IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤
                LeanProofs.GowersSzemeredi.section16LargeMultilinearFrequencyCount f P mu alpha :=
  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial hk

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let everyIndex : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d7,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L5,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L5,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L6,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L6,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d7_implies_printed,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L6_implies_printed,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L6_implies_printed,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L5,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_printed,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L5,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_implies_printed,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial
  ]
  for name in everyIndex do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the eight every-degree and every-length strengthenings, the two van der Waerden bounds, the sharper Theorem 1.3 and the polynomial Theorem 16.2 and Corollary 16.11; only approved axioms."

-- The Fejér route (Notes L.16e): `d + 6` in every degree, `L + 4` in every length.
example : ∀ d, LeanProofs.GowersSzemeredi.Theorem181AtSharp 6 d :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d6
example : ∀ L, LeanProofs.GowersSzemeredi.Theorem182AtSharp 4 L :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L4
example : ∀ L, LeanProofs.GowersSzemeredi.Corollary187AtSharp 4 L :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L4
example : LeanProofs.GowersSzemeredi.theorem_18_1 :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d6_implies_printed
example : LeanProofs.GowersSzemeredi.theorem_18_2 :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L4_implies_printed
example : LeanProofs.GowersSzemeredi.corollary_18_7 :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L4_implies_printed
example : ∀ (k r : Nat), 2 ≤ r → ∀ N : Nat,
    LeanProofs.GowersSzemeredi.szemerediThresholdAt 4 (1 / (r : Real)) k ≤ N →
      ∀ color : Nat → Fin r, LeanProofs.GowersSzemeredi.HasMonochromaticAP N r color k :=
  fun k _ hr N hN color => LeanProofs.GowersSzemeredi.van_der_waerden_L4 k hr N hN color
example : LeanProofs.GowersSzemeredi.Theorem13At 4 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L4
example : ∀ k : Nat, 1 ≤ k → LeanProofs.GowersSzemeredi.PolyCoverAt k
    (LeanProofs.GowersSzemeredi.uCount (2 ^ (2 ^ LeanProofs.GowersSzemeredi.tightMuV k))
      (LeanProofs.GowersSzemeredi.uDeg23 k))
    (LeanProofs.GowersSzemeredi.uExp (2 ^ (2 ^ LeanProofs.GowersSzemeredi.tightMuV k))
      (LeanProofs.GowersSzemeredi.uDeg23 k)) :=
  fun _ hk => LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejer hk
example : ∀ k : Nat, 2 ≤ k → ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (101 * 2 ^ k + k + 24)) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ f : ZMod N → Complex, LeanProofs.GowersSzemeredi.DiscValued f →
          ¬ LeanProofs.GowersSzemeredi.UniformOfDegree f alpha (k + 2) →
          ∃ P : LeanProofs.GowersSzemeredi.Box N (k + 1),
            ∃ mu : LeanProofs.GowersSzemeredi.Point N (k + 1) → ZMod N,
              LeanProofs.GowersSzemeredi.IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤
                LeanProofs.GowersSzemeredi.section16LargeMultilinearFrequencyCount f P mu alpha :=
  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejer hk
example : ∀ d, 12 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 5 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d5_twelve_le hd
example : ∀ L, 14 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 3 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L3_fourteen_le hL
example : ∀ L, 14 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 3 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L3_fourteen_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 3 14 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L3_fourteen_le
example : ∀ d, 13 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 4 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d4_thirteen_le hd
example : ∀ d, 9 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 5 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d5_nine_le hd
example : ∀ L, 11 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 3 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L3_eleven_le hL
example : ∀ L, 11 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 3 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L3_eleven_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 3 11 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L3_eleven_le
example : ∀ k : Nat, 1 ≤ k → LeanProofs.GowersSzemeredi.PolyCoverAt k
    (LeanProofs.GowersSzemeredi.uCount (2 ^ (2 ^ LeanProofs.GowersSzemeredi.tightMuV k))
      (2 ^ (4 * 2 ^ k + 3 * (k + 4) ^ 2 + 32)))
    (LeanProofs.GowersSzemeredi.uExp (2 ^ (2 ^ LeanProofs.GowersSzemeredi.tightMuV k))
      (2 ^ (4 * 2 ^ k + 3 * (k + 4) ^ 2 + 32))) :=
  fun _ hk => LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerS hk
example : ∀ k : Nat, 2 ≤ k → ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (32 * 2 ^ k + 9 * (k + 4) ^ 2 + k + 120)) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ f : ZMod N → Complex, LeanProofs.GowersSzemeredi.DiscValued f →
          ¬ LeanProofs.GowersSzemeredi.UniformOfDegree f alpha (k + 2) →
          ∃ P : LeanProofs.GowersSzemeredi.Box N (k + 1),
            ∃ mu : LeanProofs.GowersSzemeredi.Point N (k + 1) → ZMod N,
              LeanProofs.GowersSzemeredi.IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤
                LeanProofs.GowersSzemeredi.section16LargeMultilinearFrequencyCount f P mu alpha :=
  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerS hk
example : ∀ d, LeanProofs.GowersSzemeredi.Theorem181AtSharp 5 d :=
  LeanProofs.GowersSzemeredi.theorem_18_1_d5
example : ∀ d, 11 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 4 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d4_eleven_le hd
example : ∀ L, LeanProofs.GowersSzemeredi.Theorem182AtSharp 3 L :=
  LeanProofs.GowersSzemeredi.theorem_18_2_L3
example : ∀ L, LeanProofs.GowersSzemeredi.Corollary187AtSharp 3 L :=
  LeanProofs.GowersSzemeredi.corollary_18_7_L3
example : ∀ (k r : Nat), 2 ≤ r → ∀ N : Nat,
    LeanProofs.GowersSzemeredi.szemerediThresholdAt 3 (1 / (r : Real)) k ≤ N →
      ∀ color : Nat → Fin r, LeanProofs.GowersSzemeredi.HasMonochromaticAP N r color k :=
  fun k _ hr N hN color => LeanProofs.GowersSzemeredi.van_der_waerden_L3_all k hr N hN color
example : LeanProofs.GowersSzemeredi.Theorem13At 3 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L3
example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 2 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L2_thirteen_le hL
example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 2 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L2_thirteen_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 2 13 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L2_thirteen_le
example : ∀ d, 11 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 3 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d3_eleven_le hd
example : ∀ d, 8 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 4 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d4_eight_le hd
example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 1 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L1_thirteen_le hL
example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 1 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L1_thirteen_le hL
example : ∀ L, 10 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 2 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L2_ten_le hL
example : ∀ L, 10 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 2 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L2_ten_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 1 13 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L1_thirteen_le
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 2 10 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L2_ten_le
example : ∀ d, 17 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 2 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d2_seventeen_le hd
example : ∀ L, 19 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L0_nineteen_le hL
example : ∀ L, 19 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L0_nineteen_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 19 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_nineteen_le
example : ∀ k : Nat, 1 ≤ k → LeanProofs.GowersSzemeredi.PolyCoverAt k
    (LeanProofs.GowersSzemeredi.uCount (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegX k))
    (LeanProofs.GowersSzemeredi.uExp (2 ^ (2 ^ (4 * k + 13))) (2 ^ LeanProofs.GowersSzemeredi.tDegX k)) :=
  fun _ hk => LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerX hk
example : ∀ k : Nat, 2 ≤ k → ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
    ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (3 * LeanProofs.GowersSzemeredi.tDegX k + 6 * k + 38)) ∧
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
        ∀ f : ZMod N → Complex, LeanProofs.GowersSzemeredi.DiscValued f →
          ¬ LeanProofs.GowersSzemeredi.UniformOfDegree f alpha (k + 2) →
          ∃ P : LeanProofs.GowersSzemeredi.Box N (k + 1),
            ∃ mu : LeanProofs.GowersSzemeredi.Point N (k + 1) → ZMod N,
              LeanProofs.GowersSzemeredi.IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤
                LeanProofs.GowersSzemeredi.section16LargeMultilinearFrequencyCount f P mu alpha :=
  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerX hk
example : ∀ d, 16 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 2 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d2_sixteen_le hd
example : ∀ L, 18 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L0_eighteen_le hL
example : ∀ L, 18 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L0_eighteen_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 18 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_eighteen_le

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let fejer : Array Name := #[
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d6,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L4,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L4,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d6_implies_printed,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L4_implies_printed,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L4_implies_printed,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L4,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L4,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejer,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejer,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d5_twelve_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L3_fourteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L3_fourteen_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L3,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L3_fourteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerQ,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerQ,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_thirteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d5_nine_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L3_eleven_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L3_eleven_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L3_eleven_le,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L3_eleven_le,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerS,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerS,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d5,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d5_four_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_eleven_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L3,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L3,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L3_all,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L3,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L2_thirteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L2_thirteen_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L2,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_thirteen_le,
    ``LeanProofs.GowersSzemeredi.explicit_family_constants_poly_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d3_eleven_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_eight_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L1_thirteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L1_thirteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L1,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L1_thirteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_seventeen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L0_nineteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L0_nineteen_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L0,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_nineteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_16_2_polynomial_fejerX,
    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerX,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_sixteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L0_eighteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L0_eighteen_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L0_eighteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_eighteen_le
  ]
  for name in fejer do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "{name} is not a theorem"
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
  logInfo "Checked the Fejér-route strengthenings: Theorem 18.1 at d+6 in every degree, Theorem 18.2 and Corollary 18.7 at L+4 in every length, the van der Waerden bound and Theorem 1.3 at k+4, their printed consequences, the polynomial Theorem 16.2 and Corollary 16.11 at the Fejér classes, and d+5 (d >= 12), L+3 (L >= 14) with the van der Waerden bound and Theorem 1.3 at k+3 (k >= 14), and from the small dimension-two seed d+4 (d >= 13), d+5 (d >= 9), L+3 (L >= 11) with the van der Waerden bound and Theorem 1.3 at k+3 (k >= 11), and the polynomial Theorem 16.2 / Corollary 16.11 at its classes, and from the exact small-dimension classes d+5 in every degree, d+4 (d >= 11), L+3 in every length with the van der Waerden bound and Theorem 1.3 at k+3, and from the polynomial Bohr radius L+2 (L >= 13) with the van der Waerden bound and Theorem 1.3 at k+2 (k >= 13), and from the polynomial base budget d+3 (d >= 11), d+4 (d >= 8), L+1 (L >= 13), L+2 (L >= 10) with the van der Waerden bound and Theorem 1.3 at k+1 (k >= 13) and k+2 (k >= 10), and from class constant 5/2 d+2 (d >= 17) and L+0 (L >= 19) with the van der Waerden bound and Theorem 1.3 at k (k >= 19), and the polynomial Theorem 16.2 / Corollary 16.11 at those classes, and with the exact table to dimension 14 d+2 (d >= 16) and L+0 (L >= 18); only approved axioms."

-- The refutation is checked separately; it is never counted as a proof
-- of the original printed encoding or hidden among the 120 companions.
open Lean Elab Command in
run_cmd do
  let target := ``LeanProofs.GowersSzemeredi.lemma_16_10_printed_unit_encoding
  let proof := ``LeanProofs.GowersSzemeredi.lemma_16_10_packaged_premises_counterexample
  let info ← getConstInfo proof
  unless info.isTheorem && info.type == mkApp (mkConst ``Not) (mkConst target) do
    throwError "The Lemma 16.10 counterexample does not negate its printed encoding"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in (← collectAxioms proof) do
    unless allowed.contains axiomName do
      throwError "{proof} depends on unapproved axiom {axiomName}"
  logInfo "Separately checked the refutation of the printed Lemma 16.10 encoding."
