import Diophantine.Paper1980.System90
import IPRADerivations.Core.Order

/-!
# The positive Pell slack row in ordinary iPRA

Jones's `Sys90.E10b` uses the addition row `k = η + ζ` with positive natural
witness `ζ`. The forward construction chooses `k - η` in `NecessityPell90`.
The native consistency reduction uses this same row and positivity in
`NativePellPower.power_lt_twice_Y`, with `η = x 12` and `ζ = x 13` for the
source proof. Here the two directions are object-theory derivations with
the same row and witness convention.
-/

set_option autoImplicit false

namespace DiophantineConsistency.IPRAPellSlack

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The positive natural witness convention of `Sys90.E10b`. -/
def row (η k ζ : PTm n) : Fm PTm n :=
  LeanProofs.IPRA.lt zero ζ ⋏ (k ≐ η + ζ)

/-- The witness ranges over naturals, with its positivity in the formula. -/
def hasSlack (η k : PTm n) : Fm PTm n :=
  .ex (row (Syn.shift η) (Syn.shift k) (Syn.var 0))

private theorem row_inst (η k ζ : PTm n) :
    (row (Syn.shift η) (Syn.shift k) (Syn.var 0)).subst (Syn.inst ζ) = row η k ζ := by
  simp [row]

/-- A strict bound supplies the original canonical witness `k ∸ η`,
including the positivity guard. -/
theorem row_of_lt {η k : PTm n} (h : Γ ⊢[PRAAx] LeanProofs.IPRA.lt η k) :
    Γ ⊢[PRAAx] row η k (monus k η) := by
  let d := monus k (succ η)
  have kEquation : Γ ⊢[PRAAx] k ≐ η + succ d :=
    ((eq_add_of_le h).eqTrans (succ_add η d)).eqTrans (add_succ η d).eqSymm
  have witnessEquation : Γ ⊢[PRAAx] monus k η ≐ succ d :=
    (congrMonus kEquation (.eqRefl η)).eqTrans (add_monus' (succ d) η)
  have positiveSucc : Γ ⊢[PRAAx] LeanProofs.IPRA.lt zero (succ d) :=
    le_of_eq_add ((succ_add zero d).eqTrans (congrSucc (zero_add d))).eqSymm
  exact .andI (lt_congr (.eqRefl _) witnessEquation.eqSymm positiveSucc)
    (kEquation.eqTrans (congrAdd (.eqRefl η) witnessEquation.eqSymm))

/-- The addition equation and strict positivity imply the original bound. -/
theorem lt_of_row {η k ζ : PTm n} (h : Γ ⊢[PRAAx] row η k ζ) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.lt η k := by
  let d := monus ζ (succ zero)
  have witnessEquation : Γ ⊢[PRAAx] ζ ≐ succ d :=
    ((eq_add_of_le (Prf.andE₁ h)).eqTrans (succ_add zero d)).eqTrans
      (congrSucc (zero_add d))
  have kEquation : Γ ⊢[PRAAx] k ≐ η + succ d :=
    (Prf.andE₂ h).eqTrans (congrAdd (.eqRefl η) witnessEquation)
  exact le_of_eq_add ((kEquation.eqTrans (add_succ η d)).eqTrans (succ_add η d).eqSymm)

/-- Eliminate a strict inequality by the positive E10b witness. -/
theorem hasSlack_of_lt (η k : PTm n) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.lt η k ⟶ hasSlack η k := by
  refine .impI (.exI (monus k η) ?_)
  rw [row_inst]
  exact row_of_lt Prf.hyp0

/-- Recover strict order from a positive E10b witness. -/
theorem lt_of_hasSlack (η k : PTm n) :
    Γ ⊢[PRAAx] hasSlack η k ⟶ LeanProofs.IPRA.lt η k := by
  refine .impI (.exE Prf.hyp0 ?_)
  simpa only [Fm.shift, subst_lt, Syn.shift] using
    (lt_of_row (η := Syn.shift η) (k := Syn.shift k) (ζ := Syn.var 0) Prf.hyp0)

/-- The upper interval used in the Pell ratio bound, derived from the
adjacent E10a and E10b rows. -/
theorem upperInterval {c k Y η ζ : PTm n}
    (interval : Γ ⊢[PRAAx] c ≐ k * Y + η) (slack : Γ ⊢[PRAAx] row η k ζ) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.lt c (k * (Y + succ zero)) := by
  let d := monus k (succ η)
  have kEquation : Γ ⊢[PRAAx] k ≐ succ η + d := eq_add_of_le (lt_of_row slack)
  have upper : Γ ⊢[PRAAx] k * (Y + succ zero) ≐ k * Y + k :=
    (congrMul (.eqRefl k) (succ_eq_add_one Y).eqSymm).eqTrans (mul_succ k Y)
  have base : Γ ⊢[PRAAx] k * Y + succ η ≐ succ c :=
    (add_succ (k * Y) η).eqTrans (congrSucc interval.eqSymm)
  refine le_of_eq_add (d := d) (upper.eqTrans ?_)
  exact (congrAdd (.eqRefl (k * Y)) kEquation).eqTrans <|
    (add_assoc (k * Y) (succ η) d).eqSymm.eqTrans (congrAdd base (.eqRefl d))

/-- The exact ports of the native Pell consumer have strict order, and the
canonical constructor recovers the supplied slack port. -/
theorem nativeSourceSlack (terms : Fin 31 → PTm n)
    (hζ : Γ ⊢[PRAAx] LeanProofs.IPRA.lt zero (terms 13)) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.lt (terms 12) (terms 12 + terms 13) ⋏
      (monus (terms 12 + terms 13) (terms 12) ≐ terms 13) :=
  .andI (lt_of_row (.andI hζ (.eqRefl _))) (add_monus' (terms 13) (terms 12))

/-- Instantiate the upper interval at the exact source ports, with the
addition in the order established by `NativePellBootstrap.source_c_bounds`. -/
theorem nativeSourceUpperInterval (terms : Fin 31 → PTm n)
    (interval : Γ ⊢[PRAAx]
      terms 19 ≐ terms 12 + (terms 12 + terms 13) * (terms 16 * terms 9))
    (positive : Γ ⊢[PRAAx] LeanProofs.IPRA.lt zero (terms 13)) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.lt (terms 19)
      ((terms 12 + terms 13) * (terms 16 * terms 9 + succ zero)) :=
  upperInterval (interval.eqTrans (add_comm _ _)) (.andI positive (.eqRefl _))

/-- The external natural-number reading of the row. -/
def natRow (η k ζ : ℕ) : Prop :=
  0 < ζ ∧ k = η + ζ

/-- Read the exact E10b equation and its separate positivity hypothesis. -/
theorem natRow_of_sys90
    {x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ φ κ μ ρ Δ β ζ σ y : ℕ}
    (system : Jones1980.Sys90 x V H Tindex a b c d e f g h i j k l n o q r s t w
      α γ η θ lam τ φ κ μ ρ Δ β ζ σ y) (positive : 0 < ζ) :
    natRow η k ζ :=
  ⟨positive, system.E10b⟩

/-- The external construction used in `NecessityPell90`. -/
theorem natRow_of_lt {η k : ℕ} (h : η < k) : natRow η k (k - η) :=
  ⟨Nat.sub_pos_of_lt h, (Nat.add_sub_of_le h.le).symm⟩

theorem nat_lt_of_row {η k ζ : ℕ} (h : natRow η k ζ) : η < k := by
  rw [h.2]
  exact Nat.lt_add_of_pos_right h.1

#print axioms hasSlack_of_lt
#print axioms lt_of_hasSlack
#print axioms upperInterval
#print axioms nativeSourceSlack
#print axioms nativeSourceUpperInterval

end DiophantineConsistency.IPRAPellSlack
