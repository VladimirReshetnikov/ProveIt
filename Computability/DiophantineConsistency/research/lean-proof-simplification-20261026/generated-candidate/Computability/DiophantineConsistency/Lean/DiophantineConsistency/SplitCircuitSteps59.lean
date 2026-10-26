import DiophantineConsistency.ArithmeticDAGPowers
import DiophantineConsistency.SplitCircuit59

/-! # Local scalar equations for the pinned natural split116 parent DAG
Refactor candidate; original generator tools/generate_split_recipe_steps59.py. Intended proofs use
the actual list evaluator and its closed topology certificate. -/
namespace DiophantineConsistency.SplitCircuitSteps59
open ArithmeticDAG
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
variable {R : Type*} [CommRing R]

def naturalRegister (p : Fin 12 → R) (x : Fin 9 → R) (i : ℕ) : R :=
  (run p x SplitCircuit59.naturalNodes []).getD i 0


/-- One local-equation theorem specializes to every generated step. -/
private theorem natural_step (p : Fin 12 → R) (x : Fin 9 → R)
    (i : Fin 515) :
    naturalRegister p x i.val =
      (SplitCircuit59.naturalNodes.getD i.val (.literal 0)).evalAt p x
        (naturalRegister p x) :=
  run_node_equation p x SplitCircuit59.naturalNodes SplitCircuit59.natural_topological i.val
    (by simpa only [SplitCircuit59.natural_length] using i.isLt)

/-- Zero marks a register with no asserted pure-power specification. -/
private def naturalPowerLabels : List ℕ :=
  [
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,4,8,
    9,18,19,38,39,78,79,158,159,318,636,0,0,88,176,177,0,0,16,32,
    64,65,130,260,261,522,0,0,98,0,0,100,200,201,0,0,28,56,57,0,
    0,0,3,6,7,0,0,0,0,14,0,0,118,0,0,0,0,85,0,0,
    128,129,0,0,0,0,0,0,21,0,0,0,0,96,0,0,26,0,0,0,
    0,0,0,0,0,0,0,53,0,0,0,0,0,0,131,0,0,12,0,0,
    0,0,171,0,0,20,0,0,11,0,0,0,0,0,0,0,0,0,0,0,
    0,119,0,0,0,0,54,0,0,30,0,0,266,0,0,0,0,25,0,0,
    0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,67,
    0,0,0,0,211,0,0,0,0,0,0,0,0,0,0,0,0,80,0,0,
    154,0,0,0,0,220,0,0,0,0,0,0,60,0,0,126,0,0,31,0,
    0,0,0,0,0,41,0,0,180,0,0,49,0,0,13,0,0,0,0,0,
    0,0,0,29,0,0,164,0,0,0,0,0,0,27,0,0,0,0,0,0,
    61,36,43,34,50,109,110,112,116,91,55,101,92,107,37,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,22,0,227,0,0,148,0,0,0,0,0,0,207,0,0,
    10,0,0,68,0,0,162,0,0,0,0,0,0,117,0,0,0,0,175,0,
    0,89,0,0,40,0,0,0,0,209,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,284,568,569,1138,
    1139,2278,2279,0,0,600,1200,1201,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
  ]

private def naturalPowerLabel (i : ℕ) : ℕ := naturalPowerLabels.getD i 0

set_option maxHeartbeats 12000000 in
private theorem natural_power_certificate : ∀ i : Fin 515,
    i.val ≠ 36 → naturalPowerLabel i.val ≠ 0 →
      PowerStep SplitCircuit59.naturalNodes naturalPowerLabel i.val := by
  decide +kernel

/-- Reuses the existing generic soundness theorem for exponent labels. -/
private theorem natural_power (p : Fin 12 → R) (x : Fin 9 → R)
    (i : Fin 515) (hi : naturalPowerLabel i.val ≠ 0) :
    naturalRegister p x i.val = naturalRegister p x 36 ^ naturalPowerLabel i.val :=
  run_power p x SplitCircuit59.naturalNodes SplitCircuit59.natural_topological
    naturalPowerLabel 36 (by decide)
    (fun j hj => natural_power_certificate
      ⟨j, by simpa only [SplitCircuit59.natural_length] using hj⟩)
    i.val (by simpa only [SplitCircuit59.natural_length] using i.isLt) hi

theorem natural_step_0 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 0 = x ⟨0,by decide⟩ :=
  natural_step p x ⟨0, by decide⟩

theorem natural_step_1 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 1 = x ⟨1,by decide⟩ :=
  natural_step p x ⟨1, by decide⟩

theorem natural_step_2 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 2 = x ⟨2,by decide⟩ :=
  natural_step p x ⟨2, by decide⟩

theorem natural_step_3 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 3 = x ⟨3,by decide⟩ :=
  natural_step p x ⟨3, by decide⟩

theorem natural_step_4 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 4 = x ⟨4,by decide⟩ :=
  natural_step p x ⟨4, by decide⟩

theorem natural_step_5 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 5 = x ⟨5,by decide⟩ :=
  natural_step p x ⟨5, by decide⟩

theorem natural_step_6 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 6 = x ⟨6,by decide⟩ :=
  natural_step p x ⟨6, by decide⟩

theorem natural_step_7 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 7 = x ⟨7,by decide⟩ :=
  natural_step p x ⟨7, by decide⟩

theorem natural_step_8 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 8 = x ⟨8,by decide⟩ :=
  natural_step p x ⟨8, by decide⟩

theorem natural_step_9 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 9 = ((1 : ℤ) : R) :=
  natural_step p x ⟨9, by decide⟩

theorem natural_step_10 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 10 = naturalRegister p x 0 + naturalRegister p x 9 :=
  natural_step p x ⟨10, by decide⟩

theorem natural_step_11 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 11 = naturalRegister p x 1 + naturalRegister p x 9 :=
  natural_step p x ⟨11, by decide⟩

theorem natural_step_12 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 12 = naturalRegister p x 2 + naturalRegister p x 9 :=
  natural_step p x ⟨12, by decide⟩

theorem natural_step_13 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 13 = naturalRegister p x 3 + naturalRegister p x 9 :=
  natural_step p x ⟨13, by decide⟩

theorem natural_step_14 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 14 = naturalRegister p x 4 + naturalRegister p x 9 :=
  natural_step p x ⟨14, by decide⟩

theorem natural_step_15 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 15 = naturalRegister p x 5 + naturalRegister p x 9 :=
  natural_step p x ⟨15, by decide⟩

theorem natural_step_16 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 16 = naturalRegister p x 6 + naturalRegister p x 9 :=
  natural_step p x ⟨16, by decide⟩

theorem natural_step_17 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 17 = naturalRegister p x 8 + naturalRegister p x 9 :=
  natural_step p x ⟨17, by decide⟩

theorem natural_step_18 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 18 = ((-2 : ℤ) : R) :=
  natural_step p x ⟨18, by decide⟩

theorem natural_step_19 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 19 = p ⟨0,by decide⟩ :=
  natural_step p x ⟨19, by decide⟩

theorem natural_step_20 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 20 = ((-6 : ℤ) : R) :=
  natural_step p x ⟨20, by decide⟩

theorem natural_step_21 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 21 = ((2 : ℤ) : R) :=
  natural_step p x ⟨21, by decide⟩

theorem natural_step_22 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 22 = p ⟨1,by decide⟩ :=
  natural_step p x ⟨22, by decide⟩

theorem natural_step_23 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 23 = p ⟨2,by decide⟩ :=
  natural_step p x ⟨23, by decide⟩

theorem natural_step_24 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 24 = p ⟨3,by decide⟩ :=
  natural_step p x ⟨24, by decide⟩

theorem natural_step_25 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 25 = p ⟨4,by decide⟩ :=
  natural_step p x ⟨25, by decide⟩

theorem natural_step_26 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 26 = p ⟨5,by decide⟩ :=
  natural_step p x ⟨26, by decide⟩

theorem natural_step_27 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 27 = ((-8 : ℤ) : R) :=
  natural_step p x ⟨27, by decide⟩

theorem natural_step_28 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 28 = p ⟨6,by decide⟩ :=
  natural_step p x ⟨28, by decide⟩

theorem natural_step_29 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 29 = p ⟨7,by decide⟩ :=
  natural_step p x ⟨29, by decide⟩

theorem natural_step_30 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 30 = ((-1 : ℤ) : R) :=
  natural_step p x ⟨30, by decide⟩

theorem natural_step_31 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 31 = ((-4 : ℤ) : R) :=
  natural_step p x ⟨31, by decide⟩

theorem natural_step_32 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 32 = p ⟨8,by decide⟩ :=
  natural_step p x ⟨32, by decide⟩

theorem natural_step_33 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 33 = p ⟨9,by decide⟩ :=
  natural_step p x ⟨33, by decide⟩

theorem natural_step_34 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 34 = p ⟨10,by decide⟩ :=
  natural_step p x ⟨34, by decide⟩

theorem natural_step_35 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 35 = naturalRegister p x 10 * naturalRegister p x 10 :=
  natural_step p x ⟨35, by decide⟩

theorem natural_step_36 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 36 = naturalRegister p x 34 * naturalRegister p x 35 :=
  natural_step p x ⟨36, by decide⟩

theorem natural_step_37 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 37 = naturalRegister p x 36 * naturalRegister p x 36 :=
  natural_step p x ⟨37, by decide⟩

theorem natural_step_38 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 38 = naturalRegister p x 37 * naturalRegister p x 37 :=
  natural_step p x ⟨38, by decide⟩

theorem natural_step_39 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 39 = naturalRegister p x 38 * naturalRegister p x 38 :=
  natural_step p x ⟨39, by decide⟩

theorem natural_step_40 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 40 = naturalRegister p x 36 * naturalRegister p x 39 :=
  natural_step p x ⟨40, by decide⟩

theorem natural_step_41 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 41 = naturalRegister p x 40 * naturalRegister p x 40 :=
  natural_step p x ⟨41, by decide⟩

theorem natural_step_42 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 42 = naturalRegister p x 36 * naturalRegister p x 41 :=
  natural_step p x ⟨42, by decide⟩

theorem natural_step_43 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 43 = naturalRegister p x 42 * naturalRegister p x 42 :=
  natural_step p x ⟨43, by decide⟩

theorem natural_step_44 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 44 = naturalRegister p x 36 * naturalRegister p x 43 :=
  natural_step p x ⟨44, by decide⟩

theorem natural_step_45 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 45 = naturalRegister p x 44 * naturalRegister p x 44 :=
  natural_step p x ⟨45, by decide⟩

theorem natural_step_46 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 46 = naturalRegister p x 36 * naturalRegister p x 45 :=
  natural_step p x ⟨46, by decide⟩

theorem natural_step_47 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 47 = naturalRegister p x 46 * naturalRegister p x 46 :=
  natural_step p x ⟨47, by decide⟩

theorem natural_step_48 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 48 = naturalRegister p x 36 * naturalRegister p x 47 :=
  natural_step p x ⟨48, by decide⟩

theorem natural_step_49 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 49 = naturalRegister p x 48 * naturalRegister p x 48 :=
  natural_step p x ⟨49, by decide⟩

theorem natural_step_50 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 50 = naturalRegister p x 49 * naturalRegister p x 49 :=
  natural_step p x ⟨50, by decide⟩

theorem natural_step_51 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 51 = naturalRegister p x 20 * naturalRegister p x 50 :=
  natural_step p x ⟨51, by decide⟩

theorem natural_step_52 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 52 = naturalRegister p x 18 + naturalRegister p x 51 :=
  natural_step p x ⟨52, by decide⟩

theorem natural_step_53 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 53 = naturalRegister p x 40 * naturalRegister p x 46 :=
  natural_step p x ⟨53, by decide⟩

theorem natural_step_54 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 54 = naturalRegister p x 53 * naturalRegister p x 53 :=
  natural_step p x ⟨54, by decide⟩

theorem natural_step_55 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 55 = naturalRegister p x 36 * naturalRegister p x 54 :=
  natural_step p x ⟨55, by decide⟩

theorem natural_step_56 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 56 = naturalRegister p x 52 * naturalRegister p x 55 :=
  natural_step p x ⟨56, by decide⟩

theorem natural_step_57 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 57 = naturalRegister p x 18 + naturalRegister p x 56 :=
  natural_step p x ⟨57, by decide⟩

theorem natural_step_58 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 58 = naturalRegister p x 39 * naturalRegister p x 39 :=
  natural_step p x ⟨58, by decide⟩

theorem natural_step_59 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 59 = naturalRegister p x 58 * naturalRegister p x 58 :=
  natural_step p x ⟨59, by decide⟩

theorem natural_step_60 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 60 = naturalRegister p x 59 * naturalRegister p x 59 :=
  natural_step p x ⟨60, by decide⟩

theorem natural_step_61 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 61 = naturalRegister p x 36 * naturalRegister p x 60 :=
  natural_step p x ⟨61, by decide⟩

theorem natural_step_62 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 62 = naturalRegister p x 61 * naturalRegister p x 61 :=
  natural_step p x ⟨62, by decide⟩

theorem natural_step_63 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 63 = naturalRegister p x 62 * naturalRegister p x 62 :=
  natural_step p x ⟨63, by decide⟩

theorem natural_step_64 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 64 = naturalRegister p x 36 * naturalRegister p x 63 :=
  natural_step p x ⟨64, by decide⟩

theorem natural_step_65 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 65 = naturalRegister p x 64 * naturalRegister p x 64 :=
  natural_step p x ⟨65, by decide⟩

theorem natural_step_66 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 66 = naturalRegister p x 57 * naturalRegister p x 65 :=
  natural_step p x ⟨66, by decide⟩

theorem natural_step_67 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 67 = naturalRegister p x 19 + naturalRegister p x 66 :=
  natural_step p x ⟨67, by decide⟩

theorem natural_step_68 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 68 = naturalRegister p x 42 * naturalRegister p x 46 :=
  natural_step p x ⟨68, by decide⟩

theorem natural_step_69 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 69 = naturalRegister p x 67 * naturalRegister p x 68 :=
  natural_step p x ⟨69, by decide⟩

theorem natural_step_70 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 70 = naturalRegister p x 18 + naturalRegister p x 69 :=
  natural_step p x ⟨70, by decide⟩

theorem natural_step_71 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 71 = naturalRegister p x 37 * naturalRegister p x 68 :=
  natural_step p x ⟨71, by decide⟩

theorem natural_step_72 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 72 = naturalRegister p x 71 * naturalRegister p x 71 :=
  natural_step p x ⟨72, by decide⟩

theorem natural_step_73 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 73 = naturalRegister p x 36 * naturalRegister p x 72 :=
  natural_step p x ⟨73, by decide⟩

theorem natural_step_74 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 74 = naturalRegister p x 70 * naturalRegister p x 73 :=
  natural_step p x ⟨74, by decide⟩

theorem natural_step_75 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 75 = naturalRegister p x 18 + naturalRegister p x 74 :=
  natural_step p x ⟨75, by decide⟩

theorem natural_step_76 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 76 = naturalRegister p x 40 * naturalRegister p x 42 :=
  natural_step p x ⟨76, by decide⟩

theorem natural_step_77 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 77 = naturalRegister p x 76 * naturalRegister p x 76 :=
  natural_step p x ⟨77, by decide⟩

theorem natural_step_78 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 78 = naturalRegister p x 36 * naturalRegister p x 77 :=
  natural_step p x ⟨78, by decide⟩

theorem natural_step_79 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 79 = naturalRegister p x 75 * naturalRegister p x 78 :=
  natural_step p x ⟨79, by decide⟩

theorem natural_step_80 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 80 = naturalRegister p x 18 + naturalRegister p x 79 :=
  natural_step p x ⟨80, by decide⟩

theorem natural_step_81 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 81 = naturalRegister p x 76 * naturalRegister p x 80 :=
  natural_step p x ⟨81, by decide⟩

theorem natural_step_82 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 82 = naturalRegister p x 36 * naturalRegister p x 37 :=
  natural_step p x ⟨82, by decide⟩

theorem natural_step_83 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 83 = naturalRegister p x 82 * naturalRegister p x 82 :=
  natural_step p x ⟨83, by decide⟩

theorem natural_step_84 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 84 = naturalRegister p x 36 * naturalRegister p x 83 :=
  natural_step p x ⟨84, by decide⟩

theorem natural_step_85 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 85 = naturalRegister p x 18 * naturalRegister p x 84 :=
  natural_step p x ⟨85, by decide⟩

theorem natural_step_86 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 86 = naturalRegister p x 21 + naturalRegister p x 85 :=
  natural_step p x ⟨86, by decide⟩

theorem natural_step_87 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 87 = naturalRegister p x 40 * naturalRegister p x 86 :=
  natural_step p x ⟨87, by decide⟩

theorem natural_step_88 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 88 = naturalRegister p x 18 + naturalRegister p x 87 :=
  natural_step p x ⟨88, by decide⟩

theorem natural_step_89 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 89 = naturalRegister p x 84 * naturalRegister p x 84 :=
  natural_step p x ⟨89, by decide⟩

theorem natural_step_90 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 90 = naturalRegister p x 88 * naturalRegister p x 89 :=
  natural_step p x ⟨90, by decide⟩

theorem natural_step_91 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 91 = naturalRegister p x 21 + naturalRegister p x 90 :=
  natural_step p x ⟨91, by decide⟩

theorem natural_step_92 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 92 = naturalRegister p x 44 * naturalRegister p x 46 :=
  natural_step p x ⟨92, by decide⟩

theorem natural_step_93 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 93 = naturalRegister p x 91 * naturalRegister p x 92 :=
  natural_step p x ⟨93, by decide⟩

theorem natural_step_94 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 94 = naturalRegister p x 28 + naturalRegister p x 93 :=
  natural_step p x ⟨94, by decide⟩

theorem natural_step_95 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 95 = naturalRegister p x 83 * naturalRegister p x 94 :=
  natural_step p x ⟨95, by decide⟩

theorem natural_step_96 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 96 = naturalRegister p x 18 + naturalRegister p x 95 :=
  natural_step p x ⟨96, by decide⟩

theorem natural_step_97 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 97 = naturalRegister p x 76 * naturalRegister p x 78 :=
  natural_step p x ⟨97, by decide⟩

theorem natural_step_98 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 98 = naturalRegister p x 96 * naturalRegister p x 97 :=
  natural_step p x ⟨98, by decide⟩

theorem natural_step_99 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 99 = naturalRegister p x 18 + naturalRegister p x 98 :=
  natural_step p x ⟨99, by decide⟩

theorem natural_step_100 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 100 = naturalRegister p x 60 * naturalRegister p x 60 :=
  natural_step p x ⟨100, by decide⟩

theorem natural_step_101 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 101 = naturalRegister p x 36 * naturalRegister p x 100 :=
  natural_step p x ⟨101, by decide⟩

theorem natural_step_102 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 102 = naturalRegister p x 99 * naturalRegister p x 101 :=
  natural_step p x ⟨102, by decide⟩

theorem natural_step_103 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 103 = naturalRegister p x 21 + naturalRegister p x 102 :=
  natural_step p x ⟨103, by decide⟩

theorem natural_step_104 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 104 = naturalRegister p x 76 * naturalRegister p x 103 :=
  natural_step p x ⟨104, by decide⟩

theorem natural_step_105 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 105 = naturalRegister p x 21 + naturalRegister p x 104 :=
  natural_step p x ⟨105, by decide⟩

theorem natural_step_106 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 106 = naturalRegister p x 76 * naturalRegister p x 105 :=
  natural_step p x ⟨106, by decide⟩

theorem natural_step_107 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 107 = naturalRegister p x 27 + naturalRegister p x 106 :=
  natural_step p x ⟨107, by decide⟩

theorem natural_step_108 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 108 = naturalRegister p x 84 * naturalRegister p x 89 :=
  natural_step p x ⟨108, by decide⟩

theorem natural_step_109 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 109 = naturalRegister p x 107 * naturalRegister p x 108 :=
  natural_step p x ⟨109, by decide⟩

theorem natural_step_110 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 110 = naturalRegister p x 18 + naturalRegister p x 109 :=
  natural_step p x ⟨110, by decide⟩

theorem natural_step_111 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 111 = naturalRegister p x 58 * naturalRegister p x 110 :=
  natural_step p x ⟨111, by decide⟩

theorem natural_step_112 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 112 = naturalRegister p x 21 + naturalRegister p x 111 :=
  natural_step p x ⟨112, by decide⟩

theorem natural_step_113 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 113 = naturalRegister p x 44 * naturalRegister p x 78 :=
  natural_step p x ⟨113, by decide⟩

theorem natural_step_114 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 114 = naturalRegister p x 112 * naturalRegister p x 113 :=
  natural_step p x ⟨114, by decide⟩

theorem natural_step_115 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 115 = naturalRegister p x 26 + naturalRegister p x 114 :=
  natural_step p x ⟨115, by decide⟩

theorem natural_step_116 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 116 = naturalRegister p x 42 * naturalRegister p x 84 :=
  natural_step p x ⟨116, by decide⟩

theorem natural_step_117 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 117 = naturalRegister p x 115 * naturalRegister p x 116 :=
  natural_step p x ⟨117, by decide⟩

theorem natural_step_118 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 118 = naturalRegister p x 21 + naturalRegister p x 117 :=
  natural_step p x ⟨118, by decide⟩

theorem natural_step_119 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 119 = naturalRegister p x 53 * naturalRegister p x 118 :=
  natural_step p x ⟨119, by decide⟩

theorem natural_step_120 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 120 = naturalRegister p x 21 + naturalRegister p x 119 :=
  natural_step p x ⟨120, by decide⟩

theorem natural_step_121 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 121 = naturalRegister p x 37 * naturalRegister p x 120 :=
  natural_step p x ⟨121, by decide⟩

theorem natural_step_122 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 122 = naturalRegister p x 21 + naturalRegister p x 121 :=
  natural_step p x ⟨122, by decide⟩

theorem natural_step_123 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 123 = naturalRegister p x 108 * naturalRegister p x 122 :=
  natural_step p x ⟨123, by decide⟩

theorem natural_step_124 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 124 = naturalRegister p x 21 + naturalRegister p x 123 :=
  natural_step p x ⟨124, by decide⟩

theorem natural_step_125 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 125 = naturalRegister p x 47 * naturalRegister p x 124 :=
  natural_step p x ⟨125, by decide⟩

theorem natural_step_126 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 126 = naturalRegister p x 21 + naturalRegister p x 125 :=
  natural_step p x ⟨126, by decide⟩

theorem natural_step_127 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 127 = naturalRegister p x 59 * naturalRegister p x 108 :=
  natural_step p x ⟨127, by decide⟩

theorem natural_step_128 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 128 = naturalRegister p x 126 * naturalRegister p x 127 :=
  natural_step p x ⟨128, by decide⟩

theorem natural_step_129 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 129 = naturalRegister p x 18 + naturalRegister p x 128 :=
  natural_step p x ⟨129, by decide⟩

theorem natural_step_130 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 130 = naturalRegister p x 84 * naturalRegister p x 129 :=
  natural_step p x ⟨130, by decide⟩

theorem natural_step_131 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 131 = naturalRegister p x 21 + naturalRegister p x 130 :=
  natural_step p x ⟨131, by decide⟩

theorem natural_step_132 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 132 = naturalRegister p x 47 * naturalRegister p x 131 :=
  natural_step p x ⟨132, by decide⟩

theorem natural_step_133 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 133 = naturalRegister p x 21 + naturalRegister p x 132 :=
  natural_step p x ⟨133, by decide⟩

theorem natural_step_134 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 134 = naturalRegister p x 37 * naturalRegister p x 101 :=
  natural_step p x ⟨134, by decide⟩

theorem natural_step_135 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 135 = naturalRegister p x 133 * naturalRegister p x 134 :=
  natural_step p x ⟨135, by decide⟩

theorem natural_step_136 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 136 = naturalRegister p x 21 + naturalRegister p x 135 :=
  natural_step p x ⟨136, by decide⟩

theorem natural_step_137 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 137 = naturalRegister p x 83 * naturalRegister p x 83 :=
  natural_step p x ⟨137, by decide⟩

theorem natural_step_138 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 138 = naturalRegister p x 136 * naturalRegister p x 137 :=
  natural_step p x ⟨138, by decide⟩

theorem natural_step_139 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 139 = naturalRegister p x 21 + naturalRegister p x 138 :=
  natural_step p x ⟨139, by decide⟩

theorem natural_step_140 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 140 = naturalRegister p x 38 * naturalRegister p x 139 :=
  natural_step p x ⟨140, by decide⟩

theorem natural_step_141 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 141 = naturalRegister p x 21 + naturalRegister p x 140 :=
  natural_step p x ⟨141, by decide⟩

theorem natural_step_142 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 142 = naturalRegister p x 92 * naturalRegister p x 127 :=
  natural_step p x ⟨142, by decide⟩

theorem natural_step_143 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 143 = naturalRegister p x 141 * naturalRegister p x 142 :=
  natural_step p x ⟨143, by decide⟩

theorem natural_step_144 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 144 = naturalRegister p x 21 + naturalRegister p x 143 :=
  natural_step p x ⟨144, by decide⟩

theorem natural_step_145 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 145 = naturalRegister p x 39 * naturalRegister p x 137 :=
  natural_step p x ⟨145, by decide⟩

theorem natural_step_146 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 146 = naturalRegister p x 144 * naturalRegister p x 145 :=
  natural_step p x ⟨146, by decide⟩

theorem natural_step_147 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 147 = naturalRegister p x 21 + naturalRegister p x 146 :=
  natural_step p x ⟨147, by decide⟩

theorem natural_step_148 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 148 = naturalRegister p x 38 * naturalRegister p x 84 :=
  natural_step p x ⟨148, by decide⟩

theorem natural_step_149 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 149 = naturalRegister p x 147 * naturalRegister p x 148 :=
  natural_step p x ⟨149, by decide⟩

theorem natural_step_150 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 150 = naturalRegister p x 18 + naturalRegister p x 149 :=
  natural_step p x ⟨150, by decide⟩

theorem natural_step_151 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 151 = naturalRegister p x 78 * naturalRegister p x 150 :=
  natural_step p x ⟨151, by decide⟩

theorem natural_step_152 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 152 = naturalRegister p x 21 + naturalRegister p x 151 :=
  natural_step p x ⟨152, by decide⟩

theorem natural_step_153 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 153 = naturalRegister p x 38 * naturalRegister p x 152 :=
  natural_step p x ⟨153, by decide⟩

theorem natural_step_154 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 154 = naturalRegister p x 21 + naturalRegister p x 153 :=
  natural_step p x ⟨154, by decide⟩

theorem natural_step_155 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 155 = naturalRegister p x 38 * naturalRegister p x 154 :=
  natural_step p x ⟨155, by decide⟩

theorem natural_step_156 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 156 = naturalRegister p x 20 + naturalRegister p x 155 :=
  natural_step p x ⟨156, by decide⟩

theorem natural_step_157 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 157 = naturalRegister p x 82 * naturalRegister p x 156 :=
  natural_step p x ⟨157, by decide⟩

theorem natural_step_158 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 158 = naturalRegister p x 21 + naturalRegister p x 157 :=
  natural_step p x ⟨158, by decide⟩

theorem natural_step_159 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 159 = naturalRegister p x 43 * naturalRegister p x 158 :=
  natural_step p x ⟨159, by decide⟩

theorem natural_step_160 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 160 = naturalRegister p x 18 + naturalRegister p x 159 :=
  natural_step p x ⟨160, by decide⟩

theorem natural_step_161 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 161 = naturalRegister p x 68 * naturalRegister p x 108 :=
  natural_step p x ⟨161, by decide⟩

theorem natural_step_162 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 162 = naturalRegister p x 160 * naturalRegister p x 161 :=
  natural_step p x ⟨162, by decide⟩

theorem natural_step_163 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 163 = naturalRegister p x 25 + naturalRegister p x 162 :=
  natural_step p x ⟨163, by decide⟩

theorem natural_step_164 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 164 = naturalRegister p x 83 * naturalRegister p x 163 :=
  natural_step p x ⟨164, by decide⟩

theorem natural_step_165 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 165 = naturalRegister p x 24 + naturalRegister p x 164 :=
  natural_step p x ⟨165, by decide⟩

theorem natural_step_166 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 166 = naturalRegister p x 76 * naturalRegister p x 116 :=
  natural_step p x ⟨166, by decide⟩

theorem natural_step_167 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 167 = naturalRegister p x 165 * naturalRegister p x 166 :=
  natural_step p x ⟨167, by decide⟩

theorem natural_step_168 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 168 = naturalRegister p x 23 + naturalRegister p x 167 :=
  natural_step p x ⟨168, by decide⟩

theorem natural_step_169 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 169 = naturalRegister p x 58 * naturalRegister p x 89 :=
  natural_step p x ⟨169, by decide⟩

theorem natural_step_170 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 170 = naturalRegister p x 168 * naturalRegister p x 169 :=
  natural_step p x ⟨170, by decide⟩

theorem natural_step_171 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 171 = naturalRegister p x 21 + naturalRegister p x 170 :=
  natural_step p x ⟨171, by decide⟩

theorem natural_step_172 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 172 = naturalRegister p x 61 * naturalRegister p x 73 :=
  natural_step p x ⟨172, by decide⟩

theorem natural_step_173 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 173 = naturalRegister p x 171 * naturalRegister p x 172 :=
  natural_step p x ⟨173, by decide⟩

theorem natural_step_174 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 174 = naturalRegister p x 22 + naturalRegister p x 173 :=
  natural_step p x ⟨174, by decide⟩

theorem natural_step_175 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 175 = naturalRegister p x 36 * naturalRegister p x 174 :=
  natural_step p x ⟨175, by decide⟩

theorem natural_step_176 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 176 = naturalRegister p x 21 + naturalRegister p x 175 :=
  natural_step p x ⟨176, by decide⟩

theorem natural_step_177 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 177 = naturalRegister p x 89 * naturalRegister p x 148 :=
  natural_step p x ⟨177, by decide⟩

theorem natural_step_178 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 178 = naturalRegister p x 176 * naturalRegister p x 177 :=
  natural_step p x ⟨178, by decide⟩

theorem natural_step_179 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 179 = naturalRegister p x 18 + naturalRegister p x 178 :=
  natural_step p x ⟨179, by decide⟩

theorem natural_step_180 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 180 = naturalRegister p x 36 * naturalRegister p x 179 :=
  natural_step p x ⟨180, by decide⟩

theorem natural_step_181 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 181 = naturalRegister p x 30 + naturalRegister p x 84 :=
  natural_step p x ⟨181, by decide⟩

theorem natural_step_182 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 182 = naturalRegister p x 145 * naturalRegister p x 181 :=
  natural_step p x ⟨182, by decide⟩

theorem natural_step_183 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 183 = naturalRegister p x 9 + naturalRegister p x 182 :=
  natural_step p x ⟨183, by decide⟩

theorem natural_step_184 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 184 = naturalRegister p x 58 * naturalRegister p x 183 :=
  natural_step p x ⟨184, by decide⟩

theorem natural_step_185 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 185 = naturalRegister p x 30 + naturalRegister p x 184 :=
  natural_step p x ⟨185, by decide⟩

theorem natural_step_186 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 186 = naturalRegister p x 39 * naturalRegister p x 185 :=
  natural_step p x ⟨186, by decide⟩

theorem natural_step_187 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 187 = naturalRegister p x 33 + naturalRegister p x 186 :=
  natural_step p x ⟨187, by decide⟩

theorem natural_step_188 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 188 = naturalRegister p x 36 * naturalRegister p x 187 :=
  natural_step p x ⟨188, by decide⟩

theorem natural_step_189 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 189 = naturalRegister p x 29 + naturalRegister p x 188 :=
  natural_step p x ⟨189, by decide⟩

theorem natural_step_190 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 190 = naturalRegister p x 37 * naturalRegister p x 82 :=
  natural_step p x ⟨190, by decide⟩

theorem natural_step_191 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 191 = naturalRegister p x 189 * naturalRegister p x 190 :=
  natural_step p x ⟨191, by decide⟩

theorem natural_step_192 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 192 = naturalRegister p x 29 + naturalRegister p x 191 :=
  natural_step p x ⟨192, by decide⟩

theorem natural_step_193 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 193 = naturalRegister p x 36 * naturalRegister p x 192 :=
  natural_step p x ⟨193, by decide⟩

theorem natural_step_194 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 194 = naturalRegister p x 9 + naturalRegister p x 193 :=
  natural_step p x ⟨194, by decide⟩

theorem natural_step_195 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 195 = naturalRegister p x 177 * naturalRegister p x 194 :=
  natural_step p x ⟨195, by decide⟩

theorem natural_step_196 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 196 = naturalRegister p x 30 + naturalRegister p x 195 :=
  natural_step p x ⟨196, by decide⟩

theorem natural_step_197 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 197 = naturalRegister p x 166 * naturalRegister p x 196 :=
  natural_step p x ⟨197, by decide⟩

theorem natural_step_198 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 198 = naturalRegister p x 30 + naturalRegister p x 197 :=
  natural_step p x ⟨198, by decide⟩

theorem natural_step_199 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 199 = naturalRegister p x 44 * naturalRegister p x 76 :=
  natural_step p x ⟨199, by decide⟩

theorem natural_step_200 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 200 = naturalRegister p x 198 * naturalRegister p x 199 :=
  natural_step p x ⟨200, by decide⟩

theorem natural_step_201 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 201 = naturalRegister p x 9 + naturalRegister p x 200 :=
  natural_step p x ⟨201, by decide⟩

theorem natural_step_202 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 202 = naturalRegister p x 177 * naturalRegister p x 201 :=
  natural_step p x ⟨202, by decide⟩

theorem natural_step_203 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 203 = naturalRegister p x 18 + naturalRegister p x 202 :=
  natural_step p x ⟨203, by decide⟩

theorem natural_step_204 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 204 = naturalRegister p x 47 * naturalRegister p x 127 :=
  natural_step p x ⟨204, by decide⟩

theorem natural_step_205 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 205 = naturalRegister p x 203 * naturalRegister p x 204 :=
  natural_step p x ⟨205, by decide⟩

theorem natural_step_206 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 206 = naturalRegister p x 9 + naturalRegister p x 205 :=
  natural_step p x ⟨206, by decide⟩

theorem natural_step_207 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 207 = naturalRegister p x 37 * naturalRegister p x 206 :=
  natural_step p x ⟨207, by decide⟩

theorem natural_step_208 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 208 = naturalRegister p x 18 + naturalRegister p x 207 :=
  natural_step p x ⟨208, by decide⟩

theorem natural_step_209 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 209 = naturalRegister p x 190 * naturalRegister p x 208 :=
  natural_step p x ⟨209, by decide⟩

theorem natural_step_210 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 210 = naturalRegister p x 30 + naturalRegister p x 209 :=
  natural_step p x ⟨210, by decide⟩

theorem natural_step_211 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 211 = naturalRegister p x 40 * naturalRegister p x 210 :=
  natural_step p x ⟨211, by decide⟩

theorem natural_step_212 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 212 = naturalRegister p x 9 + naturalRegister p x 211 :=
  natural_step p x ⟨212, by decide⟩

theorem natural_step_213 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 213 = naturalRegister p x 38 * naturalRegister p x 212 :=
  natural_step p x ⟨213, by decide⟩

theorem natural_step_214 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 214 = naturalRegister p x 32 + naturalRegister p x 213 :=
  natural_step p x ⟨214, by decide⟩

theorem natural_step_215 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 215 = naturalRegister p x 82 * naturalRegister p x 214 :=
  natural_step p x ⟨215, by decide⟩

theorem natural_step_216 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 216 = naturalRegister p x 30 + naturalRegister p x 215 :=
  natural_step p x ⟨216, by decide⟩

theorem natural_step_217 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 217 = naturalRegister p x 116 * naturalRegister p x 166 :=
  natural_step p x ⟨217, by decide⟩

theorem natural_step_218 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 218 = naturalRegister p x 216 * naturalRegister p x 217 :=
  natural_step p x ⟨218, by decide⟩

theorem natural_step_219 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 219 = naturalRegister p x 30 + naturalRegister p x 218 :=
  natural_step p x ⟨219, by decide⟩

theorem natural_step_220 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 220 = naturalRegister p x 71 * naturalRegister p x 166 :=
  natural_step p x ⟨220, by decide⟩

theorem natural_step_221 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 221 = naturalRegister p x 219 * naturalRegister p x 220 :=
  natural_step p x ⟨221, by decide⟩

theorem natural_step_222 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 222 = naturalRegister p x 30 + naturalRegister p x 221 :=
  natural_step p x ⟨222, by decide⟩

theorem natural_step_223 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 223 = naturalRegister p x 89 * naturalRegister p x 222 :=
  natural_step p x ⟨223, by decide⟩

theorem natural_step_224 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 224 = naturalRegister p x 30 + naturalRegister p x 223 :=
  natural_step p x ⟨224, by decide⟩

theorem natural_step_225 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 225 = naturalRegister p x 42 * naturalRegister p x 73 :=
  natural_step p x ⟨225, by decide⟩

theorem natural_step_226 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 226 = naturalRegister p x 224 * naturalRegister p x 225 :=
  natural_step p x ⟨226, by decide⟩

theorem natural_step_227 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 227 = naturalRegister p x 18 + naturalRegister p x 226 :=
  natural_step p x ⟨227, by decide⟩

theorem natural_step_228 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 228 = naturalRegister p x 108 * naturalRegister p x 227 :=
  natural_step p x ⟨228, by decide⟩

theorem natural_step_229 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 229 = naturalRegister p x 21 + naturalRegister p x 228 :=
  natural_step p x ⟨229, by decide⟩

theorem natural_step_230 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 230 = naturalRegister p x 40 * naturalRegister p x 229 :=
  natural_step p x ⟨230, by decide⟩

theorem natural_step_231 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 231 = naturalRegister p x 30 + naturalRegister p x 230 :=
  natural_step p x ⟨231, by decide⟩

theorem natural_step_232 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 232 = naturalRegister p x 169 * naturalRegister p x 169 :=
  natural_step p x ⟨232, by decide⟩

theorem natural_step_233 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 233 = naturalRegister p x 231 * naturalRegister p x 232 :=
  natural_step p x ⟨233, by decide⟩

theorem natural_step_234 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 234 = naturalRegister p x 18 + naturalRegister p x 233 :=
  natural_step p x ⟨234, by decide⟩

theorem natural_step_235 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 235 = naturalRegister p x 43 * naturalRegister p x 53 :=
  natural_step p x ⟨235, by decide⟩

theorem natural_step_236 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 236 = naturalRegister p x 234 * naturalRegister p x 235 :=
  natural_step p x ⟨236, by decide⟩

theorem natural_step_237 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 237 = naturalRegister p x 21 + naturalRegister p x 236 :=
  natural_step p x ⟨237, by decide⟩

theorem natural_step_238 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 238 = naturalRegister p x 42 * naturalRegister p x 137 :=
  natural_step p x ⟨238, by decide⟩

theorem natural_step_239 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 239 = naturalRegister p x 237 * naturalRegister p x 238 :=
  natural_step p x ⟨239, by decide⟩

theorem natural_step_240 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 240 = naturalRegister p x 30 + naturalRegister p x 239 :=
  natural_step p x ⟨240, by decide⟩

theorem natural_step_241 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 241 = naturalRegister p x 44 * naturalRegister p x 240 :=
  natural_step p x ⟨241, by decide⟩

theorem natural_step_242 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 242 = naturalRegister p x 30 + naturalRegister p x 241 :=
  natural_step p x ⟨242, by decide⟩

theorem natural_step_243 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 243 = naturalRegister p x 60 * naturalRegister p x 242 :=
  natural_step p x ⟨243, by decide⟩

theorem natural_step_244 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 244 = naturalRegister p x 30 + naturalRegister p x 243 :=
  natural_step p x ⟨244, by decide⟩

theorem natural_step_245 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 245 = naturalRegister p x 108 * naturalRegister p x 145 :=
  natural_step p x ⟨245, by decide⟩

theorem natural_step_246 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 246 = naturalRegister p x 244 * naturalRegister p x 245 :=
  natural_step p x ⟨246, by decide⟩

theorem natural_step_247 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 247 = naturalRegister p x 29 + naturalRegister p x 246 :=
  natural_step p x ⟨247, by decide⟩

theorem natural_step_248 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 248 = naturalRegister p x 71 * naturalRegister p x 217 :=
  natural_step p x ⟨248, by decide⟩

theorem natural_step_249 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 249 = naturalRegister p x 247 * naturalRegister p x 248 :=
  natural_step p x ⟨249, by decide⟩

theorem natural_step_250 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 250 = naturalRegister p x 31 + naturalRegister p x 249 :=
  natural_step p x ⟨250, by decide⟩

theorem natural_step_251 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 251 = naturalRegister p x 76 * naturalRegister p x 108 :=
  natural_step p x ⟨251, by decide⟩

theorem natural_step_252 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 252 = naturalRegister p x 250 * naturalRegister p x 251 :=
  natural_step p x ⟨252, by decide⟩

theorem natural_step_253 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 253 = naturalRegister p x 18 + naturalRegister p x 252 :=
  natural_step p x ⟨253, by decide⟩

theorem natural_step_254 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 254 = naturalRegister p x 83 * naturalRegister p x 84 :=
  natural_step p x ⟨254, by decide⟩

theorem natural_step_255 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 255 = naturalRegister p x 253 * naturalRegister p x 254 :=
  natural_step p x ⟨255, by decide⟩

theorem natural_step_256 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 256 = naturalRegister p x 30 + naturalRegister p x 255 :=
  natural_step p x ⟨256, by decide⟩

theorem natural_step_257 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 257 = naturalRegister p x 41 * naturalRegister p x 256 :=
  natural_step p x ⟨257, by decide⟩

theorem natural_step_258 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 258 = naturalRegister p x 29 + naturalRegister p x 257 :=
  natural_step p x ⟨258, by decide⟩

theorem natural_step_259 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 259 = naturalRegister p x 38 * naturalRegister p x 258 :=
  natural_step p x ⟨259, by decide⟩

theorem natural_step_260 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 260 = naturalRegister p x 30 + naturalRegister p x 259 :=
  natural_step p x ⟨260, by decide⟩

theorem natural_step_261 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 261 = naturalRegister p x 166 * naturalRegister p x 260 :=
  natural_step p x ⟨261, by decide⟩

theorem natural_step_262 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 262 = naturalRegister p x 30 + naturalRegister p x 261 :=
  natural_step p x ⟨262, by decide⟩

theorem natural_step_263 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 263 = naturalRegister p x 58 * naturalRegister p x 254 :=
  natural_step p x ⟨263, by decide⟩

theorem natural_step_264 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 264 = naturalRegister p x 262 * naturalRegister p x 263 :=
  natural_step p x ⟨264, by decide⟩

theorem natural_step_265 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 265 = naturalRegister p x 21 + naturalRegister p x 264 :=
  natural_step p x ⟨265, by decide⟩

theorem natural_step_266 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 266 = naturalRegister p x 46 * naturalRegister p x 97 :=
  natural_step p x ⟨266, by decide⟩

theorem natural_step_267 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 267 = naturalRegister p x 265 * naturalRegister p x 266 :=
  natural_step p x ⟨267, by decide⟩

theorem natural_step_268 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 268 = naturalRegister p x 9 + naturalRegister p x 267 :=
  natural_step p x ⟨268, by decide⟩

theorem natural_step_269 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 269 = naturalRegister p x 58 * naturalRegister p x 268 :=
  natural_step p x ⟨269, by decide⟩

theorem natural_step_270 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 270 = naturalRegister p x 9 + naturalRegister p x 269 :=
  natural_step p x ⟨270, by decide⟩

theorem natural_step_271 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 271 = naturalRegister p x 89 * naturalRegister p x 270 :=
  natural_step p x ⟨271, by decide⟩

theorem natural_step_272 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 272 = naturalRegister p x 18 + naturalRegister p x 271 :=
  natural_step p x ⟨272, by decide⟩

theorem natural_step_273 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 273 = naturalRegister p x 89 * naturalRegister p x 254 :=
  natural_step p x ⟨273, by decide⟩

theorem natural_step_274 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 274 = naturalRegister p x 272 * naturalRegister p x 273 :=
  natural_step p x ⟨274, by decide⟩

theorem natural_step_275 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 275 = naturalRegister p x 30 + naturalRegister p x 274 :=
  natural_step p x ⟨275, by decide⟩

theorem natural_step_276 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 276 = naturalRegister p x 137 * naturalRegister p x 275 :=
  natural_step p x ⟨276, by decide⟩

theorem natural_step_277 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 277 = naturalRegister p x 21 + naturalRegister p x 276 :=
  natural_step p x ⟨277, by decide⟩

theorem natural_step_278 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 278 = naturalRegister p x 273 * naturalRegister p x 277 :=
  natural_step p x ⟨278, by decide⟩

theorem natural_step_279 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 279 = naturalRegister p x 29 + naturalRegister p x 278 :=
  natural_step p x ⟨279, by decide⟩

theorem natural_step_280 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 280 = naturalRegister p x 169 * naturalRegister p x 238 :=
  natural_step p x ⟨280, by decide⟩

theorem natural_step_281 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 281 = naturalRegister p x 41 * naturalRegister p x 41 :=
  natural_step p x ⟨281, by decide⟩

theorem natural_step_282 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 282 = naturalRegister p x 41 * naturalRegister p x 177 :=
  natural_step p x ⟨282, by decide⟩

theorem natural_step_283 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 283 = naturalRegister p x 41 * naturalRegister p x 58 :=
  natural_step p x ⟨283, by decide⟩

theorem natural_step_284 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 284 = naturalRegister p x 177 * naturalRegister p x 177 :=
  natural_step p x ⟨284, by decide⟩

theorem natural_step_285 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 285 = naturalRegister p x 232 * naturalRegister p x 251 :=
  natural_step p x ⟨285, by decide⟩

theorem natural_step_286 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 286 = naturalRegister p x 78 * naturalRegister p x 127 :=
  natural_step p x ⟨286, by decide⟩

theorem natural_step_287 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 287 = naturalRegister p x 59 * naturalRegister p x 217 :=
  natural_step p x ⟨287, by decide⟩

theorem natural_step_288 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 288 = naturalRegister p x 199 * naturalRegister p x 251 :=
  natural_step p x ⟨288, by decide⟩

theorem natural_step_289 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 289 = naturalRegister p x 245 * naturalRegister p x 284 :=
  natural_step p x ⟨289, by decide⟩

theorem natural_step_290 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 290 = naturalRegister p x 76 * naturalRegister p x 273 :=
  natural_step p x ⟨290, by decide⟩

theorem natural_step_291 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 291 = naturalRegister p x 232 * naturalRegister p x 245 :=
  natural_step p x ⟨291, by decide⟩

theorem natural_step_292 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 292 = naturalRegister p x 251 * naturalRegister p x 282 :=
  natural_step p x ⟨292, by decide⟩

theorem natural_step_293 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 293 = naturalRegister p x 127 * naturalRegister p x 166 :=
  natural_step p x ⟨293, by decide⟩

theorem natural_step_294 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 294 = naturalRegister p x 41 * naturalRegister p x 42 :=
  natural_step p x ⟨294, by decide⟩

theorem natural_step_295 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 295 = naturalRegister p x 36 + naturalRegister p x 84 :=
  natural_step p x ⟨295, by decide⟩

theorem natural_step_296 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 296 = naturalRegister p x 280 + naturalRegister p x 295 :=
  natural_step p x ⟨296, by decide⟩

theorem natural_step_297 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 297 = naturalRegister p x 281 + naturalRegister p x 296 :=
  natural_step p x ⟨297, by decide⟩

theorem natural_step_298 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 298 = naturalRegister p x 58 + naturalRegister p x 297 :=
  natural_step p x ⟨298, by decide⟩

theorem natural_step_299 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 299 = naturalRegister p x 97 + naturalRegister p x 298 :=
  natural_step p x ⟨299, by decide⟩

theorem natural_step_300 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 300 = naturalRegister p x 145 + naturalRegister p x 299 :=
  natural_step p x ⟨300, by decide⟩

theorem natural_step_301 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 301 = naturalRegister p x 199 + naturalRegister p x 300 :=
  natural_step p x ⟨301, by decide⟩

theorem natural_step_302 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 302 = naturalRegister p x 282 + naturalRegister p x 301 :=
  natural_step p x ⟨302, by decide⟩

theorem natural_step_303 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 303 = naturalRegister p x 148 + naturalRegister p x 302 :=
  natural_step p x ⟨303, by decide⟩

theorem natural_step_304 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 304 = naturalRegister p x 283 + naturalRegister p x 303 :=
  natural_step p x ⟨304, by decide⟩

theorem natural_step_305 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 305 = naturalRegister p x 254 + naturalRegister p x 304 :=
  natural_step p x ⟨305, by decide⟩

theorem natural_step_306 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 306 = naturalRegister p x 113 + naturalRegister p x 305 :=
  natural_step p x ⟨306, by decide⟩

theorem natural_step_307 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 307 = naturalRegister p x 217 + naturalRegister p x 306 :=
  natural_step p x ⟨307, by decide⟩

theorem natural_step_308 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 308 = naturalRegister p x 263 + naturalRegister p x 307 :=
  natural_step p x ⟨308, by decide⟩

theorem natural_step_309 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 309 = naturalRegister p x 284 + naturalRegister p x 308 :=
  natural_step p x ⟨309, by decide⟩

theorem natural_step_310 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 310 = naturalRegister p x 37 + naturalRegister p x 309 :=
  natural_step p x ⟨310, by decide⟩

theorem natural_step_311 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 311 = naturalRegister p x 285 + naturalRegister p x 310 :=
  natural_step p x ⟨311, by decide⟩

theorem natural_step_312 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 312 = naturalRegister p x 286 + naturalRegister p x 311 :=
  natural_step p x ⟨312, by decide⟩

theorem natural_step_313 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 313 = naturalRegister p x 287 + naturalRegister p x 312 :=
  natural_step p x ⟨313, by decide⟩

theorem natural_step_314 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 314 = naturalRegister p x 288 + naturalRegister p x 313 :=
  natural_step p x ⟨314, by decide⟩

theorem natural_step_315 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 315 = naturalRegister p x 289 + naturalRegister p x 314 :=
  natural_step p x ⟨315, by decide⟩

theorem natural_step_316 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 316 = naturalRegister p x 127 + naturalRegister p x 315 :=
  natural_step p x ⟨316, by decide⟩

theorem natural_step_317 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 317 = naturalRegister p x 290 + naturalRegister p x 316 :=
  natural_step p x ⟨317, by decide⟩

theorem natural_step_318 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 318 = naturalRegister p x 273 + naturalRegister p x 317 :=
  natural_step p x ⟨318, by decide⟩

theorem natural_step_319 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 319 = naturalRegister p x 291 + naturalRegister p x 318 :=
  natural_step p x ⟨319, by decide⟩

theorem natural_step_320 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 320 = naturalRegister p x 292 + naturalRegister p x 319 :=
  natural_step p x ⟨320, by decide⟩

theorem natural_step_321 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 321 = naturalRegister p x 40 + naturalRegister p x 320 :=
  natural_step p x ⟨321, by decide⟩

theorem natural_step_322 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 322 = naturalRegister p x 293 + naturalRegister p x 321 :=
  natural_step p x ⟨322, by decide⟩

theorem natural_step_323 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 323 = naturalRegister p x 294 + naturalRegister p x 322 :=
  natural_step p x ⟨323, by decide⟩

theorem natural_step_324 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 324 = naturalRegister p x 232 + naturalRegister p x 323 :=
  natural_step p x ⟨324, by decide⟩

theorem natural_step_325 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 325 = naturalRegister p x 148 * naturalRegister p x 148 :=
  natural_step p x ⟨325, by decide⟩

theorem natural_step_326 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 326 = naturalRegister p x 9 + naturalRegister p x 325 :=
  natural_step p x ⟨326, by decide⟩

theorem natural_step_327 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 327 = naturalRegister p x 92 * naturalRegister p x 285 :=
  natural_step p x ⟨327, by decide⟩

theorem natural_step_328 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 328 = naturalRegister p x 326 * naturalRegister p x 327 :=
  natural_step p x ⟨328, by decide⟩

theorem natural_step_329 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 329 = naturalRegister p x 9 + naturalRegister p x 328 :=
  natural_step p x ⟨329, by decide⟩

theorem natural_step_330 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 330 = naturalRegister p x 53 * naturalRegister p x 232 :=
  natural_step p x ⟨330, by decide⟩

theorem natural_step_331 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 331 = naturalRegister p x 329 * naturalRegister p x 330 :=
  natural_step p x ⟨331, by decide⟩

theorem natural_step_332 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 332 = naturalRegister p x 9 + naturalRegister p x 331 :=
  natural_step p x ⟨332, by decide⟩

theorem natural_step_333 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 333 = naturalRegister p x 254 * naturalRegister p x 332 :=
  natural_step p x ⟨333, by decide⟩

theorem natural_step_334 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 334 = naturalRegister p x 9 + naturalRegister p x 333 :=
  natural_step p x ⟨334, by decide⟩

theorem natural_step_335 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 335 = naturalRegister p x 245 * naturalRegister p x 334 :=
  natural_step p x ⟨335, by decide⟩

theorem natural_step_336 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 336 = naturalRegister p x 9 + naturalRegister p x 335 :=
  natural_step p x ⟨336, by decide⟩

theorem natural_step_337 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 337 = naturalRegister p x 71 * naturalRegister p x 293 :=
  natural_step p x ⟨337, by decide⟩

theorem natural_step_338 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 338 = naturalRegister p x 336 * naturalRegister p x 337 :=
  natural_step p x ⟨338, by decide⟩

theorem natural_step_339 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 339 = naturalRegister p x 9 + naturalRegister p x 338 :=
  natural_step p x ⟨339, by decide⟩

theorem natural_step_340 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 340 = naturalRegister p x 190 * naturalRegister p x 190 :=
  natural_step p x ⟨340, by decide⟩

theorem natural_step_341 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 341 = naturalRegister p x 339 * naturalRegister p x 340 :=
  natural_step p x ⟨341, by decide⟩

theorem natural_step_342 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 342 = naturalRegister p x 9 + naturalRegister p x 341 :=
  natural_step p x ⟨342, by decide⟩

theorem natural_step_343 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 343 = naturalRegister p x 283 * naturalRegister p x 283 :=
  natural_step p x ⟨343, by decide⟩

theorem natural_step_344 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 344 = naturalRegister p x 342 * naturalRegister p x 343 :=
  natural_step p x ⟨344, by decide⟩

theorem natural_step_345 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 345 = naturalRegister p x 9 + naturalRegister p x 344 :=
  natural_step p x ⟨345, by decide⟩

theorem natural_step_346 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 346 = naturalRegister p x 60 * naturalRegister p x 68 :=
  natural_step p x ⟨346, by decide⟩

theorem natural_step_347 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 347 = naturalRegister p x 345 * naturalRegister p x 346 :=
  natural_step p x ⟨347, by decide⟩

theorem natural_step_348 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 348 = naturalRegister p x 9 + naturalRegister p x 347 :=
  natural_step p x ⟨348, by decide⟩

theorem natural_step_349 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 349 = naturalRegister p x 42 * naturalRegister p x 348 :=
  natural_step p x ⟨349, by decide⟩

theorem natural_step_350 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 350 = naturalRegister p x 9 + naturalRegister p x 349 :=
  natural_step p x ⟨350, by decide⟩

theorem natural_step_351 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 351 = naturalRegister p x 101 * naturalRegister p x 350 :=
  natural_step p x ⟨351, by decide⟩

theorem natural_step_352 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 352 = naturalRegister p x 9 + naturalRegister p x 351 :=
  natural_step p x ⟨352, by decide⟩

theorem natural_step_353 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 353 = naturalRegister p x 78 * naturalRegister p x 232 :=
  natural_step p x ⟨353, by decide⟩

theorem natural_step_354 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 354 = naturalRegister p x 352 * naturalRegister p x 353 :=
  natural_step p x ⟨354, by decide⟩

theorem natural_step_355 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 355 = naturalRegister p x 9 + naturalRegister p x 354 :=
  natural_step p x ⟨355, by decide⟩

theorem natural_step_356 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 356 = naturalRegister p x 232 * naturalRegister p x 355 :=
  natural_step p x ⟨356, by decide⟩

theorem natural_step_357 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 357 = naturalRegister p x 9 + naturalRegister p x 356 :=
  natural_step p x ⟨357, by decide⟩

theorem natural_step_358 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 358 = naturalRegister p x 46 * naturalRegister p x 113 :=
  natural_step p x ⟨358, by decide⟩

theorem natural_step_359 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 359 = naturalRegister p x 357 * naturalRegister p x 358 :=
  natural_step p x ⟨359, by decide⟩

theorem natural_step_360 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 360 = naturalRegister p x 9 + naturalRegister p x 359 :=
  natural_step p x ⟨360, by decide⟩

theorem natural_step_361 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 361 = naturalRegister p x 44 * naturalRegister p x 284 :=
  natural_step p x ⟨361, by decide⟩

theorem natural_step_362 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 362 = naturalRegister p x 360 * naturalRegister p x 361 :=
  natural_step p x ⟨362, by decide⟩

theorem natural_step_363 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 363 = naturalRegister p x 9 + naturalRegister p x 362 :=
  natural_step p x ⟨363, by decide⟩

theorem natural_step_364 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 364 = naturalRegister p x 145 * naturalRegister p x 145 :=
  natural_step p x ⟨364, by decide⟩

theorem natural_step_365 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 365 = naturalRegister p x 363 * naturalRegister p x 364 :=
  natural_step p x ⟨365, by decide⟩

theorem natural_step_366 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 366 = naturalRegister p x 9 + naturalRegister p x 365 :=
  natural_step p x ⟨366, by decide⟩

theorem natural_step_367 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 367 = naturalRegister p x 40 * naturalRegister p x 366 :=
  natural_step p x ⟨367, by decide⟩

theorem natural_step_368 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 368 = naturalRegister p x 9 + naturalRegister p x 367 :=
  natural_step p x ⟨368, by decide⟩

theorem natural_step_369 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 369 = naturalRegister p x 71 * naturalRegister p x 285 :=
  natural_step p x ⟨369, by decide⟩

theorem natural_step_370 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 370 = naturalRegister p x 368 * naturalRegister p x 369 :=
  natural_step p x ⟨370, by decide⟩

theorem natural_step_371 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 371 = naturalRegister p x 9 + naturalRegister p x 370 :=
  natural_step p x ⟨371, by decide⟩

theorem natural_step_372 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 372 = naturalRegister p x 68 * naturalRegister p x 371 :=
  natural_step p x ⟨372, by decide⟩

theorem natural_step_373 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 373 = naturalRegister p x 9 + naturalRegister p x 372 :=
  natural_step p x ⟨373, by decide⟩

theorem natural_step_374 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 374 = naturalRegister p x 73 * naturalRegister p x 373 :=
  natural_step p x ⟨374, by decide⟩

theorem natural_step_375 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 375 = naturalRegister p x 9 + naturalRegister p x 374 :=
  natural_step p x ⟨375, by decide⟩

theorem natural_step_376 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 376 = naturalRegister p x 78 * naturalRegister p x 375 :=
  natural_step p x ⟨376, by decide⟩

theorem natural_step_377 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 377 = naturalRegister p x 9 + naturalRegister p x 376 :=
  natural_step p x ⟨377, by decide⟩

theorem natural_step_378 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 378 = naturalRegister p x 76 * naturalRegister p x 377 :=
  natural_step p x ⟨378, by decide⟩

theorem natural_step_379 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 379 = naturalRegister p x 353 - naturalRegister p x 9 :=
  natural_step p x ⟨379, by decide⟩

theorem natural_step_380 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 380 = naturalRegister p x 10 - naturalRegister p x 9 :=
  natural_step p x ⟨380, by decide⟩

theorem natural_step_381 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 381 = naturalRegister p x 324 * naturalRegister p x 380 :=
  natural_step p x ⟨381, by decide⟩

theorem natural_step_382 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 382 = naturalRegister p x 379 - naturalRegister p x 381 :=
  natural_step p x ⟨382, by decide⟩

theorem natural_step_383 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 383 = naturalRegister p x 36 - naturalRegister p x 21 :=
  natural_step p x ⟨383, by decide⟩

theorem natural_step_384 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 384 = naturalRegister p x 378 * naturalRegister p x 383 :=
  natural_step p x ⟨384, by decide⟩

theorem natural_step_385 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 385 = naturalRegister p x 353 * naturalRegister p x 384 :=
  natural_step p x ⟨385, by decide⟩

theorem natural_step_386 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 386 = naturalRegister p x 382 + naturalRegister p x 385 :=
  natural_step p x ⟨386, by decide⟩

theorem natural_step_387 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 387 = naturalRegister p x 11 + naturalRegister p x 324 :=
  natural_step p x ⟨387, by decide⟩

theorem natural_step_388 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 388 = naturalRegister p x 279 * naturalRegister p x 387 :=
  natural_step p x ⟨388, by decide⟩

theorem natural_step_389 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 389 = naturalRegister p x 180 + naturalRegister p x 388 :=
  natural_step p x ⟨389, by decide⟩

theorem natural_step_390 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 390 = naturalRegister p x 387 * naturalRegister p x 389 :=
  natural_step p x ⟨390, by decide⟩

theorem natural_step_391 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 391 = naturalRegister p x 81 + naturalRegister p x 390 :=
  natural_step p x ⟨391, by decide⟩

theorem natural_step_392 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 392 = naturalRegister p x 21 * naturalRegister p x 391 :=
  natural_step p x ⟨392, by decide⟩

theorem natural_step_393 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 393 = naturalRegister p x 378 + naturalRegister p x 392 :=
  natural_step p x ⟨393, by decide⟩

theorem natural_step_394 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 394 = naturalRegister p x 353 * naturalRegister p x 393 :=
  natural_step p x ⟨394, by decide⟩

theorem natural_step_395 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 395 = naturalRegister p x 11 + naturalRegister p x 394 :=
  natural_step p x ⟨395, by decide⟩

theorem natural_step_396 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 396 = naturalRegister p x 62 * naturalRegister p x 220 :=
  natural_step p x ⟨396, by decide⟩

theorem natural_step_397 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 397 = naturalRegister p x 396 * naturalRegister p x 396 :=
  natural_step p x ⟨397, by decide⟩

theorem natural_step_398 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 398 = naturalRegister p x 36 * naturalRegister p x 397 :=
  natural_step p x ⟨398, by decide⟩

theorem natural_step_399 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 399 = naturalRegister p x 398 * naturalRegister p x 398 :=
  natural_step p x ⟨399, by decide⟩

theorem natural_step_400 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 400 = naturalRegister p x 36 * naturalRegister p x 399 :=
  natural_step p x ⟨400, by decide⟩

theorem natural_step_401 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 401 = naturalRegister p x 400 * naturalRegister p x 400 :=
  natural_step p x ⟨401, by decide⟩

theorem natural_step_402 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 402 = naturalRegister p x 36 * naturalRegister p x 401 :=
  natural_step p x ⟨402, by decide⟩

theorem natural_step_403 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 403 = naturalRegister p x 10 * naturalRegister p x 402 :=
  natural_step p x ⟨403, by decide⟩

theorem natural_step_404 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 404 = p ⟨11,by decide⟩ :=
  natural_step p x ⟨404, by decide⟩

theorem natural_step_405 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 405 = naturalRegister p x 238 * naturalRegister p x 398 :=
  natural_step p x ⟨405, by decide⟩

theorem natural_step_406 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 406 = naturalRegister p x 405 * naturalRegister p x 405 :=
  natural_step p x ⟨406, by decide⟩

theorem natural_step_407 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 407 = naturalRegister p x 36 * naturalRegister p x 406 :=
  natural_step p x ⟨407, by decide⟩

theorem natural_step_408 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 408 = naturalRegister p x 10 * naturalRegister p x 404 :=
  natural_step p x ⟨408, by decide⟩

theorem natural_step_409 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 409 = naturalRegister p x 407 * naturalRegister p x 408 :=
  natural_step p x ⟨409, by decide⟩

theorem natural_step_410 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 410 = naturalRegister p x 386 + naturalRegister p x 395 :=
  natural_step p x ⟨410, by decide⟩

theorem natural_step_411 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 411 = naturalRegister p x 9 + naturalRegister p x 410 :=
  natural_step p x ⟨411, by decide⟩

theorem natural_step_412 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 412 = naturalRegister p x 403 * naturalRegister p x 411 :=
  natural_step p x ⟨412, by decide⟩

theorem natural_step_413 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 413 = naturalRegister p x 412 - naturalRegister p x 395 :=
  natural_step p x ⟨413, by decide⟩

theorem natural_step_414 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 414 = naturalRegister p x 413 - naturalRegister p x 9 :=
  natural_step p x ⟨414, by decide⟩

theorem natural_step_415 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 415 = naturalRegister p x 10 * naturalRegister p x 288 :=
  natural_step p x ⟨415, by decide⟩

theorem natural_step_416 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 416 = naturalRegister p x 409 * naturalRegister p x 409 :=
  natural_step p x ⟨416, by decide⟩

theorem natural_step_417 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 417 = naturalRegister p x 14 * naturalRegister p x 416 :=
  natural_step p x ⟨417, by decide⟩

theorem natural_step_418 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 418 = naturalRegister p x 13 * naturalRegister p x 416 :=
  natural_step p x ⟨418, by decide⟩

theorem natural_step_419 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 419 = naturalRegister p x 414 * naturalRegister p x 418 :=
  natural_step p x ⟨419, by decide⟩

theorem natural_step_420 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 420 = naturalRegister p x 419 * naturalRegister p x 419 :=
  natural_step p x ⟨420, by decide⟩

theorem natural_step_421 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 421 = naturalRegister p x 21 * naturalRegister p x 420 :=
  natural_step p x ⟨421, by decide⟩

theorem natural_step_422 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 422 = naturalRegister p x 417 * naturalRegister p x 421 :=
  natural_step p x ⟨422, by decide⟩

theorem natural_step_423 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 423 = naturalRegister p x 422 - naturalRegister p x 9 :=
  natural_step p x ⟨423, by decide⟩

theorem natural_step_424 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 424 = naturalRegister p x 12 * naturalRegister p x 423 :=
  natural_step p x ⟨424, by decide⟩

theorem natural_step_425 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 425 = naturalRegister p x 9 + naturalRegister p x 414 :=
  natural_step p x ⟨425, by decide⟩

theorem natural_step_426 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 426 = naturalRegister p x 424 + naturalRegister p x 425 :=
  natural_step p x ⟨426, by decide⟩

theorem natural_step_427 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 427 = naturalRegister p x 9 + naturalRegister p x 417 :=
  natural_step p x ⟨427, by decide⟩

theorem natural_step_428 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 428 = naturalRegister p x 419 * naturalRegister p x 427 :=
  natural_step p x ⟨428, by decide⟩

theorem natural_step_429 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 429 = naturalRegister p x 21 * naturalRegister p x 414 :=
  natural_step p x ⟨429, by decide⟩

theorem natural_step_430 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 430 = naturalRegister p x 9 + naturalRegister p x 429 :=
  natural_step p x ⟨430, by decide⟩

theorem natural_step_431 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 431 = naturalRegister p x 10 * naturalRegister p x 14 :=
  natural_step p x ⟨431, by decide⟩

theorem natural_step_432 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 432 = ((4 : ℤ) : R) :=
  natural_step p x ⟨432, by decide⟩

theorem natural_step_433 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 433 = naturalRegister p x 428 * naturalRegister p x 432 :=
  natural_step p x ⟨433, by decide⟩

theorem natural_step_434 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 434 = ((5 : ℤ) : R) :=
  natural_step p x ⟨434, by decide⟩

theorem natural_step_435 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 435 = naturalRegister p x 433 - naturalRegister p x 434 :=
  natural_step p x ⟨435, by decide⟩

theorem natural_step_436 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 436 = ((3 : ℤ) : R) :=
  natural_step p x ⟨436, by decide⟩

theorem natural_step_437 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 437 = naturalRegister p x 15 * naturalRegister p x 436 :=
  natural_step p x ⟨437, by decide⟩

theorem natural_step_438 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 438 = naturalRegister p x 21 * naturalRegister p x 431 :=
  natural_step p x ⟨438, by decide⟩

theorem natural_step_439 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 439 = naturalRegister p x 437 - naturalRegister p x 438 :=
  natural_step p x ⟨439, by decide⟩

theorem natural_step_440 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 440 = naturalRegister p x 431 * naturalRegister p x 439 :=
  natural_step p x ⟨440, by decide⟩

theorem natural_step_441 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 441 = naturalRegister p x 21 + naturalRegister p x 440 :=
  natural_step p x ⟨441, by decide⟩

theorem natural_step_442 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 442 = naturalRegister p x 428 * naturalRegister p x 428 :=
  natural_step p x ⟨442, by decide⟩

theorem natural_step_443 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 443 = naturalRegister p x 442 - naturalRegister p x 9 :=
  natural_step p x ⟨443, by decide⟩

theorem natural_step_444 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 444 = naturalRegister p x 15 * naturalRegister p x 15 :=
  natural_step p x ⟨444, by decide⟩

theorem natural_step_445 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 445 = naturalRegister p x 443 * naturalRegister p x 444 :=
  natural_step p x ⟨445, by decide⟩

theorem natural_step_446 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 446 = naturalRegister p x 9 + naturalRegister p x 445 :=
  natural_step p x ⟨446, by decide⟩

theorem natural_step_447 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 447 = naturalRegister p x 16 * naturalRegister p x 435 :=
  natural_step p x ⟨447, by decide⟩

theorem natural_step_448 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 448 = naturalRegister p x 15 * naturalRegister p x 447 :=
  natural_step p x ⟨448, by decide⟩

theorem natural_step_449 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 449 = naturalRegister p x 446 * naturalRegister p x 448 :=
  natural_step p x ⟨449, by decide⟩

theorem natural_step_450 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 450 = naturalRegister p x 15 * naturalRegister p x 449 :=
  natural_step p x ⟨450, by decide⟩

theorem natural_step_451 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 451 = naturalRegister p x 450 * naturalRegister p x 450 :=
  natural_step p x ⟨451, by decide⟩

theorem natural_step_452 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 452 = naturalRegister p x 443 * naturalRegister p x 451 :=
  natural_step p x ⟨452, by decide⟩

theorem natural_step_453 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 453 = naturalRegister p x 9 + naturalRegister p x 452 :=
  natural_step p x ⟨453, by decide⟩

theorem natural_step_454 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 454 = naturalRegister p x 15 * naturalRegister p x 446 :=
  natural_step p x ⟨454, by decide⟩

theorem natural_step_455 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 455 = naturalRegister p x 9 + naturalRegister p x 454 :=
  natural_step p x ⟨455, by decide⟩

theorem natural_step_456 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 456 = naturalRegister p x 455 - naturalRegister p x 428 :=
  natural_step p x ⟨456, by decide⟩

theorem natural_step_457 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 457 = naturalRegister p x 453 * naturalRegister p x 456 :=
  natural_step p x ⟨457, by decide⟩

theorem natural_step_458 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 458 = naturalRegister p x 428 + naturalRegister p x 457 :=
  natural_step p x ⟨458, by decide⟩

theorem natural_step_459 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 459 = naturalRegister p x 7 * naturalRegister p x 15 :=
  natural_step p x ⟨459, by decide⟩

theorem natural_step_460 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 460 = naturalRegister p x 430 + naturalRegister p x 459 :=
  natural_step p x ⟨460, by decide⟩

theorem natural_step_461 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 461 = naturalRegister p x 453 * naturalRegister p x 460 :=
  natural_step p x ⟨461, by decide⟩

theorem natural_step_462 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 462 = naturalRegister p x 15 + naturalRegister p x 461 :=
  natural_step p x ⟨462, by decide⟩

theorem natural_step_463 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 463 = naturalRegister p x 458 * naturalRegister p x 462 :=
  natural_step p x ⟨463, by decide⟩

theorem natural_step_464 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 464 = naturalRegister p x 463 * naturalRegister p x 463 :=
  natural_step p x ⟨464, by decide⟩

theorem natural_step_465 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 465 = naturalRegister p x 462 * naturalRegister p x 462 :=
  natural_step p x ⟨465, by decide⟩

theorem natural_step_466 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 466 = naturalRegister p x 464 - naturalRegister p x 465 :=
  natural_step p x ⟨466, by decide⟩

theorem natural_step_467 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 467 = naturalRegister p x 9 + naturalRegister p x 466 :=
  natural_step p x ⟨467, by decide⟩

theorem natural_step_468 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 468 = naturalRegister p x 422 * naturalRegister p x 426 :=
  natural_step p x ⟨468, by decide⟩

theorem natural_step_469 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 469 = naturalRegister p x 468 * naturalRegister p x 468 :=
  natural_step p x ⟨469, by decide⟩

theorem natural_step_470 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 470 = naturalRegister p x 426 * naturalRegister p x 426 :=
  natural_step p x ⟨470, by decide⟩

theorem natural_step_471 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 471 = naturalRegister p x 469 - naturalRegister p x 470 :=
  natural_step p x ⟨471, by decide⟩

theorem natural_step_472 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 472 = naturalRegister p x 9 + naturalRegister p x 471 :=
  natural_step p x ⟨472, by decide⟩

theorem natural_step_473 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 473 = naturalRegister p x 446 * naturalRegister p x 453 :=
  natural_step p x ⟨473, by decide⟩

theorem natural_step_474 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 474 = naturalRegister p x 467 * naturalRegister p x 473 :=
  natural_step p x ⟨474, by decide⟩

theorem natural_step_475 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 475 = naturalRegister p x 415 * naturalRegister p x 432 :=
  natural_step p x ⟨475, by decide⟩

theorem natural_step_476 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 476 = naturalRegister p x 475 - naturalRegister p x 11 :=
  natural_step p x ⟨476, by decide⟩

theorem natural_step_477 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 477 = naturalRegister p x 470 * naturalRegister p x 476 :=
  natural_step p x ⟨477, by decide⟩

theorem natural_step_478 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 478 = ((16 : ℤ) : R) :=
  natural_step p x ⟨478, by decide⟩

theorem natural_step_479 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 479 = naturalRegister p x 418 * naturalRegister p x 426 :=
  natural_step p x ⟨479, by decide⟩

theorem natural_step_480 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 480 = naturalRegister p x 15 - naturalRegister p x 479 :=
  natural_step p x ⟨480, by decide⟩

theorem natural_step_481 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 481 = naturalRegister p x 480 * naturalRegister p x 480 :=
  natural_step p x ⟨481, by decide⟩

theorem natural_step_482 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 482 = naturalRegister p x 415 * naturalRegister p x 478 :=
  natural_step p x ⟨482, by decide⟩

theorem natural_step_483 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 483 = naturalRegister p x 481 * naturalRegister p x 482 :=
  natural_step p x ⟨483, by decide⟩

theorem natural_step_484 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 484 = naturalRegister p x 477 - naturalRegister p x 483 :=
  natural_step p x ⟨484, by decide⟩

theorem natural_step_485 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 485 = ((8 : ℤ) : R) :=
  natural_step p x ⟨485, by decide⟩

theorem natural_step_486 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 486 = naturalRegister p x 446 * naturalRegister p x 446 :=
  natural_step p x ⟨486, by decide⟩

theorem natural_step_487 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 487 = naturalRegister p x 485 * naturalRegister p x 486 :=
  natural_step p x ⟨487, by decide⟩

theorem natural_step_488 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 488 = naturalRegister p x 432 * naturalRegister p x 446 :=
  natural_step p x ⟨488, by decide⟩

theorem natural_step_489 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 489 = naturalRegister p x 487 - naturalRegister p x 488 :=
  natural_step p x ⟨489, by decide⟩

theorem natural_step_490 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 490 = naturalRegister p x 489 - naturalRegister p x 9 :=
  natural_step p x ⟨490, by decide⟩

theorem natural_step_491 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 491 = naturalRegister p x 448 * naturalRegister p x 490 :=
  natural_step p x ⟨491, by decide⟩

theorem natural_step_492 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 492 = naturalRegister p x 463 * naturalRegister p x 491 :=
  natural_step p x ⟨492, by decide⟩

theorem natural_step_493 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 493 = naturalRegister p x 435 * naturalRegister p x 484 :=
  natural_step p x ⟨493, by decide⟩

theorem natural_step_494 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 494 = naturalRegister p x 431 * naturalRegister p x 431 :=
  natural_step p x ⟨494, by decide⟩

theorem natural_step_495 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 495 = naturalRegister p x 17 + naturalRegister p x 494 :=
  natural_step p x ⟨495, by decide⟩

theorem natural_step_496 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 496 = naturalRegister p x 435 * naturalRegister p x 495 :=
  natural_step p x ⟨496, by decide⟩

theorem natural_step_497 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 497 = naturalRegister p x 441 + naturalRegister p x 496 :=
  natural_step p x ⟨497, by decide⟩

theorem natural_step_498 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 498 = naturalRegister p x 468 + naturalRegister p x 492 :=
  natural_step p x ⟨498, by decide⟩

theorem natural_step_499 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 499 = naturalRegister p x 493 * naturalRegister p x 498 :=
  natural_step p x ⟨499, by decide⟩

theorem natural_step_500 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 500 = naturalRegister p x 497 - naturalRegister p x 499 :=
  natural_step p x ⟨500, by decide⟩

theorem natural_step_501 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 501 = naturalRegister p x 500 * naturalRegister p x 500 :=
  natural_step p x ⟨501, by decide⟩

theorem natural_step_502 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 502 = naturalRegister p x 493 * naturalRegister p x 493 :=
  natural_step p x ⟨502, by decide⟩

theorem natural_step_503 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 503 = ((64 : ℤ) : R) :=
  natural_step p x ⟨503, by decide⟩

theorem natural_step_504 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 504 = naturalRegister p x 474 * naturalRegister p x 503 :=
  natural_step p x ⟨504, by decide⟩

theorem natural_step_505 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 505 = naturalRegister p x 472 + naturalRegister p x 504 :=
  natural_step p x ⟨505, by decide⟩

theorem natural_step_506 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 506 = naturalRegister p x 502 * naturalRegister p x 505 :=
  natural_step p x ⟨506, by decide⟩

theorem natural_step_507 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 507 = naturalRegister p x 501 - naturalRegister p x 506 :=
  natural_step p x ⟨507, by decide⟩

theorem natural_step_508 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 508 = naturalRegister p x 507 * naturalRegister p x 507 :=
  natural_step p x ⟨508, by decide⟩

theorem natural_step_509 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 509 = ((256 : ℤ) : R) :=
  natural_step p x ⟨509, by decide⟩

theorem natural_step_510 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 510 = naturalRegister p x 502 * naturalRegister p x 502 :=
  natural_step p x ⟨510, by decide⟩

theorem natural_step_511 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 511 = naturalRegister p x 509 * naturalRegister p x 510 :=
  natural_step p x ⟨511, by decide⟩

theorem natural_step_512 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 512 = naturalRegister p x 472 * naturalRegister p x 511 :=
  natural_step p x ⟨512, by decide⟩

theorem natural_step_513 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 513 = naturalRegister p x 474 * naturalRegister p x 512 :=
  natural_step p x ⟨513, by decide⟩

theorem natural_step_514 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 514 = naturalRegister p x 508 - naturalRegister p x 513 :=
  natural_step p x ⟨514, by decide⟩

theorem natural_power_37 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 37 = naturalRegister p x 36 ^ 2 :=
  natural_power p x ⟨37, by decide⟩ (by decide)

theorem natural_power_38 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 38 = naturalRegister p x 36 ^ 4 :=
  natural_power p x ⟨38, by decide⟩ (by decide)

theorem natural_power_39 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 39 = naturalRegister p x 36 ^ 8 :=
  natural_power p x ⟨39, by decide⟩ (by decide)

theorem natural_power_40 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 40 = naturalRegister p x 36 ^ 9 :=
  natural_power p x ⟨40, by decide⟩ (by decide)

theorem natural_power_41 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 41 = naturalRegister p x 36 ^ 18 :=
  natural_power p x ⟨41, by decide⟩ (by decide)

theorem natural_power_42 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 42 = naturalRegister p x 36 ^ 19 :=
  natural_power p x ⟨42, by decide⟩ (by decide)

theorem natural_power_43 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 43 = naturalRegister p x 36 ^ 38 :=
  natural_power p x ⟨43, by decide⟩ (by decide)

theorem natural_power_44 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 44 = naturalRegister p x 36 ^ 39 :=
  natural_power p x ⟨44, by decide⟩ (by decide)

theorem natural_power_45 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 45 = naturalRegister p x 36 ^ 78 :=
  natural_power p x ⟨45, by decide⟩ (by decide)

theorem natural_power_46 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 46 = naturalRegister p x 36 ^ 79 :=
  natural_power p x ⟨46, by decide⟩ (by decide)

theorem natural_power_47 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 47 = naturalRegister p x 36 ^ 158 :=
  natural_power p x ⟨47, by decide⟩ (by decide)

theorem natural_power_48 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 48 = naturalRegister p x 36 ^ 159 :=
  natural_power p x ⟨48, by decide⟩ (by decide)

theorem natural_power_49 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 49 = naturalRegister p x 36 ^ 318 :=
  natural_power p x ⟨49, by decide⟩ (by decide)

theorem natural_power_50 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 50 = naturalRegister p x 36 ^ 636 :=
  natural_power p x ⟨50, by decide⟩ (by decide)

theorem natural_power_53 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 53 = naturalRegister p x 36 ^ 88 :=
  natural_power p x ⟨53, by decide⟩ (by decide)

theorem natural_power_54 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 54 = naturalRegister p x 36 ^ 176 :=
  natural_power p x ⟨54, by decide⟩ (by decide)

theorem natural_power_55 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 55 = naturalRegister p x 36 ^ 177 :=
  natural_power p x ⟨55, by decide⟩ (by decide)

theorem natural_power_58 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 58 = naturalRegister p x 36 ^ 16 :=
  natural_power p x ⟨58, by decide⟩ (by decide)

theorem natural_power_59 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 59 = naturalRegister p x 36 ^ 32 :=
  natural_power p x ⟨59, by decide⟩ (by decide)

theorem natural_power_60 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 60 = naturalRegister p x 36 ^ 64 :=
  natural_power p x ⟨60, by decide⟩ (by decide)

theorem natural_power_61 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 61 = naturalRegister p x 36 ^ 65 :=
  natural_power p x ⟨61, by decide⟩ (by decide)

theorem natural_power_62 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 62 = naturalRegister p x 36 ^ 130 :=
  natural_power p x ⟨62, by decide⟩ (by decide)

theorem natural_power_63 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 63 = naturalRegister p x 36 ^ 260 :=
  natural_power p x ⟨63, by decide⟩ (by decide)

theorem natural_power_64 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 64 = naturalRegister p x 36 ^ 261 :=
  natural_power p x ⟨64, by decide⟩ (by decide)

theorem natural_power_65 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 65 = naturalRegister p x 36 ^ 522 :=
  natural_power p x ⟨65, by decide⟩ (by decide)

theorem natural_power_68 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 68 = naturalRegister p x 36 ^ 98 :=
  natural_power p x ⟨68, by decide⟩ (by decide)

theorem natural_power_71 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 71 = naturalRegister p x 36 ^ 100 :=
  natural_power p x ⟨71, by decide⟩ (by decide)

theorem natural_power_72 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 72 = naturalRegister p x 36 ^ 200 :=
  natural_power p x ⟨72, by decide⟩ (by decide)

theorem natural_power_73 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 73 = naturalRegister p x 36 ^ 201 :=
  natural_power p x ⟨73, by decide⟩ (by decide)

theorem natural_power_76 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 76 = naturalRegister p x 36 ^ 28 :=
  natural_power p x ⟨76, by decide⟩ (by decide)

theorem natural_power_77 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 77 = naturalRegister p x 36 ^ 56 :=
  natural_power p x ⟨77, by decide⟩ (by decide)

theorem natural_power_78 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 78 = naturalRegister p x 36 ^ 57 :=
  natural_power p x ⟨78, by decide⟩ (by decide)

theorem natural_power_82 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 82 = naturalRegister p x 36 ^ 3 :=
  natural_power p x ⟨82, by decide⟩ (by decide)

theorem natural_power_83 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 83 = naturalRegister p x 36 ^ 6 :=
  natural_power p x ⟨83, by decide⟩ (by decide)

theorem natural_power_84 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 84 = naturalRegister p x 36 ^ 7 :=
  natural_power p x ⟨84, by decide⟩ (by decide)

theorem natural_power_89 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 89 = naturalRegister p x 36 ^ 14 :=
  natural_power p x ⟨89, by decide⟩ (by decide)

theorem natural_power_92 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 92 = naturalRegister p x 36 ^ 118 :=
  natural_power p x ⟨92, by decide⟩ (by decide)

theorem natural_power_97 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 97 = naturalRegister p x 36 ^ 85 :=
  natural_power p x ⟨97, by decide⟩ (by decide)

theorem natural_power_100 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 100 = naturalRegister p x 36 ^ 128 :=
  natural_power p x ⟨100, by decide⟩ (by decide)

theorem natural_power_101 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 101 = naturalRegister p x 36 ^ 129 :=
  natural_power p x ⟨101, by decide⟩ (by decide)

theorem natural_power_108 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 108 = naturalRegister p x 36 ^ 21 :=
  natural_power p x ⟨108, by decide⟩ (by decide)

theorem natural_power_113 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 113 = naturalRegister p x 36 ^ 96 :=
  natural_power p x ⟨113, by decide⟩ (by decide)

theorem natural_power_116 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 116 = naturalRegister p x 36 ^ 26 :=
  natural_power p x ⟨116, by decide⟩ (by decide)

theorem natural_power_127 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 127 = naturalRegister p x 36 ^ 53 :=
  natural_power p x ⟨127, by decide⟩ (by decide)

theorem natural_power_134 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 134 = naturalRegister p x 36 ^ 131 :=
  natural_power p x ⟨134, by decide⟩ (by decide)

theorem natural_power_137 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 137 = naturalRegister p x 36 ^ 12 :=
  natural_power p x ⟨137, by decide⟩ (by decide)

theorem natural_power_142 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 142 = naturalRegister p x 36 ^ 171 :=
  natural_power p x ⟨142, by decide⟩ (by decide)

theorem natural_power_145 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 145 = naturalRegister p x 36 ^ 20 :=
  natural_power p x ⟨145, by decide⟩ (by decide)

theorem natural_power_148 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 148 = naturalRegister p x 36 ^ 11 :=
  natural_power p x ⟨148, by decide⟩ (by decide)

theorem natural_power_161 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 161 = naturalRegister p x 36 ^ 119 :=
  natural_power p x ⟨161, by decide⟩ (by decide)

theorem natural_power_166 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 166 = naturalRegister p x 36 ^ 54 :=
  natural_power p x ⟨166, by decide⟩ (by decide)

theorem natural_power_169 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 169 = naturalRegister p x 36 ^ 30 :=
  natural_power p x ⟨169, by decide⟩ (by decide)

theorem natural_power_172 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 172 = naturalRegister p x 36 ^ 266 :=
  natural_power p x ⟨172, by decide⟩ (by decide)

theorem natural_power_177 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 177 = naturalRegister p x 36 ^ 25 :=
  natural_power p x ⟨177, by decide⟩ (by decide)

theorem natural_power_190 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 190 = naturalRegister p x 36 ^ 5 :=
  natural_power p x ⟨190, by decide⟩ (by decide)

theorem natural_power_199 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 199 = naturalRegister p x 36 ^ 67 :=
  natural_power p x ⟨199, by decide⟩ (by decide)

theorem natural_power_204 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 204 = naturalRegister p x 36 ^ 211 :=
  natural_power p x ⟨204, by decide⟩ (by decide)

theorem natural_power_217 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 217 = naturalRegister p x 36 ^ 80 :=
  natural_power p x ⟨217, by decide⟩ (by decide)

theorem natural_power_220 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 220 = naturalRegister p x 36 ^ 154 :=
  natural_power p x ⟨220, by decide⟩ (by decide)

theorem natural_power_225 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 225 = naturalRegister p x 36 ^ 220 :=
  natural_power p x ⟨225, by decide⟩ (by decide)

theorem natural_power_232 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 232 = naturalRegister p x 36 ^ 60 :=
  natural_power p x ⟨232, by decide⟩ (by decide)

theorem natural_power_235 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 235 = naturalRegister p x 36 ^ 126 :=
  natural_power p x ⟨235, by decide⟩ (by decide)

theorem natural_power_238 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 238 = naturalRegister p x 36 ^ 31 :=
  natural_power p x ⟨238, by decide⟩ (by decide)

theorem natural_power_245 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 245 = naturalRegister p x 36 ^ 41 :=
  natural_power p x ⟨245, by decide⟩ (by decide)

theorem natural_power_248 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 248 = naturalRegister p x 36 ^ 180 :=
  natural_power p x ⟨248, by decide⟩ (by decide)

theorem natural_power_251 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 251 = naturalRegister p x 36 ^ 49 :=
  natural_power p x ⟨251, by decide⟩ (by decide)

theorem natural_power_254 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 254 = naturalRegister p x 36 ^ 13 :=
  natural_power p x ⟨254, by decide⟩ (by decide)

theorem natural_power_263 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 263 = naturalRegister p x 36 ^ 29 :=
  natural_power p x ⟨263, by decide⟩ (by decide)

theorem natural_power_266 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 266 = naturalRegister p x 36 ^ 164 :=
  natural_power p x ⟨266, by decide⟩ (by decide)

theorem natural_power_273 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 273 = naturalRegister p x 36 ^ 27 :=
  natural_power p x ⟨273, by decide⟩ (by decide)

theorem natural_power_280 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 280 = naturalRegister p x 36 ^ 61 :=
  natural_power p x ⟨280, by decide⟩ (by decide)

theorem natural_power_281 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 281 = naturalRegister p x 36 ^ 36 :=
  natural_power p x ⟨281, by decide⟩ (by decide)

theorem natural_power_282 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 282 = naturalRegister p x 36 ^ 43 :=
  natural_power p x ⟨282, by decide⟩ (by decide)

theorem natural_power_283 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 283 = naturalRegister p x 36 ^ 34 :=
  natural_power p x ⟨283, by decide⟩ (by decide)

theorem natural_power_284 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 284 = naturalRegister p x 36 ^ 50 :=
  natural_power p x ⟨284, by decide⟩ (by decide)

theorem natural_power_285 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 285 = naturalRegister p x 36 ^ 109 :=
  natural_power p x ⟨285, by decide⟩ (by decide)

theorem natural_power_286 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 286 = naturalRegister p x 36 ^ 110 :=
  natural_power p x ⟨286, by decide⟩ (by decide)

theorem natural_power_287 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 287 = naturalRegister p x 36 ^ 112 :=
  natural_power p x ⟨287, by decide⟩ (by decide)

theorem natural_power_288 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 288 = naturalRegister p x 36 ^ 116 :=
  natural_power p x ⟨288, by decide⟩ (by decide)

theorem natural_power_289 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 289 = naturalRegister p x 36 ^ 91 :=
  natural_power p x ⟨289, by decide⟩ (by decide)

theorem natural_power_290 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 290 = naturalRegister p x 36 ^ 55 :=
  natural_power p x ⟨290, by decide⟩ (by decide)

theorem natural_power_291 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 291 = naturalRegister p x 36 ^ 101 :=
  natural_power p x ⟨291, by decide⟩ (by decide)

theorem natural_power_292 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 292 = naturalRegister p x 36 ^ 92 :=
  natural_power p x ⟨292, by decide⟩ (by decide)

theorem natural_power_293 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 293 = naturalRegister p x 36 ^ 107 :=
  natural_power p x ⟨293, by decide⟩ (by decide)

theorem natural_power_294 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 294 = naturalRegister p x 36 ^ 37 :=
  natural_power p x ⟨294, by decide⟩ (by decide)

theorem natural_power_325 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 325 = naturalRegister p x 36 ^ 22 :=
  natural_power p x ⟨325, by decide⟩ (by decide)

theorem natural_power_327 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 327 = naturalRegister p x 36 ^ 227 :=
  natural_power p x ⟨327, by decide⟩ (by decide)

theorem natural_power_330 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 330 = naturalRegister p x 36 ^ 148 :=
  natural_power p x ⟨330, by decide⟩ (by decide)

theorem natural_power_337 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 337 = naturalRegister p x 36 ^ 207 :=
  natural_power p x ⟨337, by decide⟩ (by decide)

theorem natural_power_340 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 340 = naturalRegister p x 36 ^ 10 :=
  natural_power p x ⟨340, by decide⟩ (by decide)

theorem natural_power_343 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 343 = naturalRegister p x 36 ^ 68 :=
  natural_power p x ⟨343, by decide⟩ (by decide)

theorem natural_power_346 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 346 = naturalRegister p x 36 ^ 162 :=
  natural_power p x ⟨346, by decide⟩ (by decide)

theorem natural_power_353 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 353 = naturalRegister p x 36 ^ 117 :=
  natural_power p x ⟨353, by decide⟩ (by decide)

theorem natural_power_358 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 358 = naturalRegister p x 36 ^ 175 :=
  natural_power p x ⟨358, by decide⟩ (by decide)

theorem natural_power_361 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 361 = naturalRegister p x 36 ^ 89 :=
  natural_power p x ⟨361, by decide⟩ (by decide)

theorem natural_power_364 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 364 = naturalRegister p x 36 ^ 40 :=
  natural_power p x ⟨364, by decide⟩ (by decide)

theorem natural_power_369 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 369 = naturalRegister p x 36 ^ 209 :=
  natural_power p x ⟨369, by decide⟩ (by decide)

theorem natural_power_396 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 396 = naturalRegister p x 36 ^ 284 :=
  natural_power p x ⟨396, by decide⟩ (by decide)

theorem natural_power_397 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 397 = naturalRegister p x 36 ^ 568 :=
  natural_power p x ⟨397, by decide⟩ (by decide)

theorem natural_power_398 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 398 = naturalRegister p x 36 ^ 569 :=
  natural_power p x ⟨398, by decide⟩ (by decide)

theorem natural_power_399 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 399 = naturalRegister p x 36 ^ 1138 :=
  natural_power p x ⟨399, by decide⟩ (by decide)

theorem natural_power_400 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 400 = naturalRegister p x 36 ^ 1139 :=
  natural_power p x ⟨400, by decide⟩ (by decide)

theorem natural_power_401 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 401 = naturalRegister p x 36 ^ 2278 :=
  natural_power p x ⟨401, by decide⟩ (by decide)

theorem natural_power_402 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 402 = naturalRegister p x 36 ^ 2279 :=
  natural_power p x ⟨402, by decide⟩ (by decide)

theorem natural_power_405 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 405 = naturalRegister p x 36 ^ 600 :=
  natural_power p x ⟨405, by decide⟩ (by decide)

theorem natural_power_406 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 406 = naturalRegister p x 36 ^ 1200 :=
  natural_power p x ⟨406, by decide⟩ (by decide)

theorem natural_power_407 (p : Fin 12 → R) (x : Fin 9 → R) :
    naturalRegister p x 407 = naturalRegister p x 36 ^ 1201 :=
  natural_power p x ⟨407, by decide⟩ (by decide)

end DiophantineConsistency.SplitCircuitSteps59
