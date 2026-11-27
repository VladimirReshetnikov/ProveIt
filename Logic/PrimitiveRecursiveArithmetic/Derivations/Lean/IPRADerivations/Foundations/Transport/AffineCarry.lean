import IPRADerivations.Core.Powers
import IPRADerivations.Core.Tactic

/-!
Packet: `foundations/ipra_transport_framework_2026-11-20`. Imported from the packet's `lean/AffineCarry.lean`:
the iterated affine map `carry` (`x ↦ xL + b`, `j` times) with `start`, `advance`, `stepSound`, `carry_identity`,
`closedCarry` (`carry_j(x) = carry_j(0) + L^j x`, by quantifier-free induction).

 The uniform amplification identity, with an object-level iteration count. -/
namespace LeanProofs.IPRA.Foundations.Transport.Affine
open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (app zero succ)

abbrev seed : PTm 3 := var 2
abbrev tick : PTm 5 := (var 1 : PTm 5) * var 2 + var 3

def carry {n} (j L b x : PTm n) : PTm n :=
  app (recDef seed tick) (Fin.cases j ![L, b, x])

variable {n : Nat} {Γ : List (Fm PTm n)}

@[simp] theorem subst_carry {m : Nat} (σ : Fin n → PTm m) (j L b x : PTm n) :
    Syn.subst σ (carry j L b x) = carry (Syn.subst σ j) (Syn.subst σ L)
      (Syn.subst σ b) (Syn.subst σ x) := by
  unfold carry
  rw [LeanProofs.ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem start (L b x : PTm n) : Γ ⊢[PRAAx] carry zero L b x ≐ x :=
  rec_zero seed tick ![L,b,x]

theorem advance (j L b x : PTm n) :
    Γ ⊢[PRAAx] carry (succ j) L b x ≐ carry j L b x * L + b := by
  have h : Γ ⊢[PRAAx] carry (succ j) L b x ≐ Syn.subst ![j,carry j L b x,L,b,x] tick :=
    rec_succ_vecCons seed tick j ![L,b,x]
  simpa [tick] using h

def invariant : Fm PTm 4 :=
  carry (var 0) (var 1) (var 2) (var 3) ≐
  carry (var 0) (var 1) (var 2) zero + pw (var 1) (var 0) * var 3

theorem stepSound (j L b x : PTm n)
    (ih : Γ ⊢[PRAAx] carry j L b x ≐ carry j L b zero + pw L j * x) :
    Γ ⊢[PRAAx] carry (succ j) L b x ≐ carry (succ j) L b zero + pw L (succ j) * x := by
  refine (advance j L b x).eqTrans ?_
  refine (congrAdd (congrMul ih (.eqRefl L)) (.eqRefl b)).eqTrans ?_
  refine Prf.eqTrans ?_ (congrAdd (advance j L b zero).eqSymm
    (congrMul (pw_succ L j).eqSymm (.eqRefl x)))
  ipra_ring

theorem carry_identity : ([] : List (Fm PTm 4)) ⊢[PRAAx] invariant := by
  refine ind invariant trivial ?_ ?_
  · ipra_ind_simp [invariant, subst_carry, pw, subst_ap2]
    refine (start _ _ _).eqTrans (Prf.eqSymm ?_)
    refine (congrAdd (start _ _ _) (congrMul (pw_zero _) (.eqRefl _))).eqTrans ?_
    exact (zero_add _).eqTrans (one_mul _)
  · ipra_ind_simp [invariant, subst_carry, pw, subst_ap2]
    exact stepSound _ _ _ _ Prf.hyp0

theorem closedCarry : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 invariant :=
  closeUniv 4 carry_identity

end LeanProofs.IPRA.Foundations.Transport.Affine
