import DiophantineConsistency.Source34.Source34Ports
import DiophantineConsistency.ArithmeticStandardCasts
import DiophantineConsistency.ModelDifferenceRing

/-! # The six fixed integers of package 138's 924/107 equation

Package 138 (`con-zfc-diophantine-forms/138-semantic-signs/integer11`) fixes six
integers `beta, K0, MC, MF, cone_A, cone_B`. The first four are exactly the
source34 tuple `Source34Ports.ports` (with `MF` already shifted by `beta`, as
`Source34Ports.ports 3 = beta + MF_native`); the two cones are the powers of two
`cone_A = 2^1113` and `cone_B = 2^666104` of `PROOF.md`.

All six stay symbolic natural numbers (`ports6`). This module proves, in every
model `V` of `𝗜𝚺₁`, the facts about their images in the ring of differences
`DiffRing V` that the soundness modules use, packaged as `PortFacts portsR`:

* `beta + 1 = 2^1064921` (as `Exp.exp`), `beta = 6m + 1`, `2^64 ≤ beta`;
* `0 ≤ K0`, `0 ≤ MC < beta`, `0 ≤ MF < 2 beta` (`Source34Ports.leaf_bounds`);
* `cone_A = 2^1113`, `cone_B = 2^666104` (as `Exp.exp` and as ring powers), both
  multiples of sixteen and at least eight.

No numeral is evaluated: every concrete projection goes through a lemma proved
for arbitrary arguments (the reason is recorded in `Source34Ports`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Ports
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing

/-! ## The six ports as natural numbers -/

def coneA : ℕ := 2^1113
def coneB : ℕ := 2^666104

/-- Six-entry vectors, with projections proved for arbitrary entries. -/
def vec6 (a b c d e f : ℕ) : Fin 6 → ℕ := ![a, b, c, d, e, f]

theorem vec6_zero (a b c d e f : ℕ) : vec6 a b c d e f 0 = a := rfl
theorem vec6_one (a b c d e f : ℕ) : vec6 a b c d e f 1 = b := rfl
theorem vec6_two (a b c d e f : ℕ) : vec6 a b c d e f 2 = c := rfl
theorem vec6_three (a b c d e f : ℕ) : vec6 a b c d e f 3 = d := rfl
theorem vec6_four (a b c d e f : ℕ) : vec6 a b c d e f 4 = e := rfl
theorem vec6_five (a b c d e f : ℕ) : vec6 a b c d e f 5 = f := rfl

/-- The port tuple `beta, K0, MC, MF (shifted), cone_A, cone_B`. -/
def ports6 : Fin 6 → ℕ :=
  vec6 (Source34Ports.ports 0) (Source34Ports.ports 1) (Source34Ports.ports 2)
    (Source34Ports.ports 3) coneA coneB

attribute [local irreducible] Source34Ports.betaNat Source34Ports.lowNat Source34Ports.highNat
  Source34Kernel.paramKernel Mixed121Kernel.rho coneA coneB

theorem ports6_zero : ports6 0 = Source34Ports.betaNat := by
  unfold ports6 Source34Ports.ports
  rw [vec6_zero, Source34Ports.ports_zero]

theorem ports6_four : ports6 4 = coneA := by unfold ports6; rw [vec6_four]
theorem ports6_five : ports6 5 = coneB := by unfold ports6; rw [vec6_five]

/-! ## Natural-number facts -/

theorem two_pow_odd_mod_six (k : ℕ) : 2^(2*k+1) % 6 = 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h : 2^(2*(k+1)+1) = 4 * 2^(2*k+1) := by
      rw [show 2*(k+1)+1 = (2*k+1) + 2 by ring, pow_add]; ring
    rw [h]
    generalize 2^(2*k+1) = Q at ih ⊢
    omega

theorem beta_mod_six : Source34Ports.betaNat % 6 = 1 := by
  unfold Source34Ports.betaNat
  have h := two_pow_odd_mod_six 532460
  rw [show 2*532460+1 = 121*8801 by norm_num] at h
  have hpos : 2 ≤ 2^(121*8801) := Nat.le_self_pow (by norm_num) 2
  generalize 2^(121*8801) = Q at h hpos ⊢
  omega

theorem beta_ge_pow : 2^64 ≤ Source34Ports.betaNat := by
  unfold Source34Ports.betaNat
  have h : 2^64 < 2^(121*8801) := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  generalize 2^(121*8801) = Q at h ⊢
  generalize 2^64 = T at h ⊢
  omega

/-! ## Model forms -/

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The ports in the ring of differences, as the literal reads them. -/
def portsR : Fin 6 → DiffRing V := fun i => (((ports6 i : ℕ) : ℤ) : DiffRing V)

theorem portsR_eq (i : Fin 6) : portsR (V := V) i = ι ((ports6 i : ℕ) : V) := by
  unfold portsR
  rw [Int.cast_natCast, ← map_natCast ι]

theorem coneA_model : ((coneA : ℕ) : V) = Exp.exp (1113 : V) := by
  have h := ArithmeticStandardCasts.cast_exp (V := V) 1113
  rw [Nat.cast_ofNat] at h
  unfold coneA
  rw [h]

theorem coneB_model : ((coneB : ℕ) : V) = Exp.exp (666104 : V) := by
  have h := ArithmeticStandardCasts.cast_exp (V := V) 666104
  rw [Nat.cast_ofNat] at h
  unfold coneB
  rw [h]

theorem coneA_pow : ((coneA : ℕ) : DiffRing V) = 2^1113 := by
  unfold coneA; rw [Nat.cast_pow, Nat.cast_ofNat]

theorem coneB_pow : ((coneB : ℕ) : DiffRing V) = 2^666104 := by
  unfold coneB; rw [Nat.cast_pow, Nat.cast_ofNat]

theorem p0_eq : portsR (V := V) 0 = ι (Exp.exp (1064921 : V)) - 1 := by
  rw [portsR_eq, ports6_zero]
  have h := Source34Ports.beta_identity (V := V)
  rw [show (121:V)*8801 = 1064921 by norm_num] at h
  rw [← h, map_add, map_one, add_sub_cancel_right]

theorem p4_eq : portsR (V := V) 4 = 2^1113 := by
  unfold portsR; rw [ports6_four, Int.cast_natCast, coneA_pow]

theorem p5_eq : portsR (V := V) 5 = 2^666104 := by
  unfold portsR; rw [ports6_five, Int.cast_natCast, coneB_pow]

theorem p4_exp : portsR (V := V) 4 = ι (Exp.exp (1113 : V)) := by
  rw [portsR_eq, ports6_four, coneA_model]

theorem p5_exp : portsR (V := V) 5 = ι (Exp.exp (666104 : V)) := by
  rw [portsR_eq, ports6_five, coneB_model]

/-- The facts about the six ports used by the soundness modules. -/
structure PortFacts (p : Fin 6 → DiffRing V) : Prop where
  beta_exp : p 0 + 1 = ι (Exp.exp (1064921 : V))
  beta_mod : ∃ m : DiffRing V, p 0 = 6 * m + 1
  beta_ge : (2:DiffRing V)^64 ≤ p 0
  K0_nonneg : 0 ≤ p 1
  MC_nonneg : 0 ≤ p 2
  MC_lt : p 2 < p 0
  MF_nonneg : 0 ≤ p 3
  MF_lt : p 3 < 2 * p 0
  coneA_exp : p 4 = ι (Exp.exp (1113 : V))
  coneB_exp : p 5 = ι (Exp.exp (666104 : V))
  coneA_pow : p 4 = 2^1113
  coneB_pow : p 5 = 2^666104
  coneA_sixteen : ∃ m : DiffRing V, p 4 = 16 * m
  coneB_sixteen : ∃ m : DiffRing V, p 5 = 16 * m
  coneA_ge : 8 ≤ p 4
  coneB_ge : 8 ≤ p 5

theorem sixteen_dvd_pow (n : ℕ) (hn : 4 ≤ n) : ∃ m : DiffRing V, (2:DiffRing V)^n = 16 * m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨2^k, by rw [pow_add]; norm_num⟩

theorem eight_le_pow (n : ℕ) (hn : 3 ≤ n) : (8:DiffRing V) ≤ (2:DiffRing V)^n := by
  have h : (2:DiffRing V)^3 ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn
  norm_num at h
  exact h

/-- **The port facts hold at the literal's ports.** -/
theorem portFacts : PortFacts (portsR (V := V)) := by
  obtain ⟨hb0, hlow, hhigh, _⟩ := Source34Ports.leaf_bounds (V := V)
  have ι0 : portsR (V := V) 0 = ι ((Source34Ports.ports 0 : ℕ) : V) := by
    rw [portsR_eq]; unfold ports6; rw [vec6_zero]
  have ι1 : portsR (V := V) 1 = ι ((Source34Ports.ports 1 : ℕ) : V) := by
    rw [portsR_eq]; unfold ports6; rw [vec6_one]
  have ι2 : portsR (V := V) 2 = ι ((Source34Ports.ports 2 : ℕ) : V) := by
    rw [portsR_eq]; unfold ports6; rw [vec6_two]
  have ι3 : portsR (V := V) 3 = ι ((Source34Ports.ports 3 : ℕ) : V) := by
    rw [portsR_eq]; unfold ports6; rw [vec6_three]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, p4_exp, p5_exp, p4_eq, p5_eq, ?_, ?_, ?_, ?_⟩
  · rw [p0_eq, sub_add_cancel]
  · have h := Nat.div_add_mod Source34Ports.betaNat 6
    rw [beta_mod_six] at h
    refine ⟨(((Source34Ports.betaNat / 6 : ℕ) : ℤ) : DiffRing V), ?_⟩
    rw [portsR, ports6_zero]
    conv_lhs => rw [← h]
    push_cast
    ring
  · rw [portsR, ports6_zero]
    have h : ((2^64 : ℕ) : DiffRing V) ≤ ((Source34Ports.betaNat : ℕ) : DiffRing V) :=
      Nat.cast_le.mpr beta_ge_pow
    rw [Nat.cast_pow, Nat.cast_ofNat] at h
    rw [Int.cast_natCast]
    exact h
  · rw [ι1]; exact ι_nonneg _
  · rw [ι2]; exact ι_nonneg _
  · rw [ι2, ι0]; exact ι_lt_ι.mpr hlow
  · rw [ι3]; exact ι_nonneg _
  · rw [ι3, ι0, show (2:DiffRing V) = ι 2 by rw [map_ofNat], ← map_mul]
    exact ι_lt_ι.mpr hhigh
  · rw [p4_eq]; exact sixteen_dvd_pow 1113 (by norm_num)
  · rw [p5_eq]; exact sixteen_dvd_pow 666104 (by norm_num)
  · rw [p4_eq]; exact eight_le_pow 1113 (by norm_num)
  · rw [p5_eq]; exact eight_le_pow 666104 (by norm_num)

#print axioms ports6_zero
#print axioms beta_mod_six
#print axioms beta_ge_pow
#print axioms coneA_model
#print axioms coneB_model
#print axioms p0_eq
#print axioms portFacts

end DiophantineConsistency.P138Ports
