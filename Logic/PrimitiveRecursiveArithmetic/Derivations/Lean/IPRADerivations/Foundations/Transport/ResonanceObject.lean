import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.Tactic
import IPRADerivations.Core.CertificateTactics

/-!
Packet: `foundations/ipra_transport_framework_2026-11-20`. Imported from the packet's `lean/ResonanceObject.lean`:
the cross-multiplied coefficient telescope with a variable horizon (`advance`, `origin`, `telescope`,
`exceptional`, `closedExceptional`) and the first resonance logarithm (`firstLogSound`, `closedFirstLog`).

 Object-iPRA cross-multiplied coefficient telescope with a variable horizon.
a, b, v are fixed two-argument PR terms. x is any numerical parameter, which
can contain coded arrays. Both recurrence guards appear inside the closed
sentence. There are no positivity assumptions and no cancellations. -/
namespace LeanProofs.IPRA.Foundations.Transport.ResonanceObject
open LeanProofs.ConciseIPRA LeanProofs.IPRA Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (zero succ)
variable {n : Nat} {Γ : List (Fm PTm n)}

abbrev prod (b : PTm 2) (k x : PTm n) := ap2 (prodF b) k x

theorem prodStep (body : PTm 2) (k x : PTm n) :
    Γ ⊢[PRAAx] prod body (succ k) x ≐ prod body k x * inst2 body k x :=
  prod_succ body k x

abbrev RecStep (a b v : PTm 2) (j x : PTm n) : Fm PTm n :=
  inst2 b j x * inst2 v (succ j) x ≐ inst2 a j x * inst2 v j x

abbrev Inv (a b v : PTm 2) (k x : PTm n) : Fm PTm n :=
  prod b k x * inst2 v k x ≐ prod a k x * inst2 v zero x

theorem advance (a b v : PTm 2) (j x : PTm n)
    (hr : Γ ⊢[PRAAx] RecStep a b v j x) (hi : Γ ⊢[PRAAx] Inv a b v j x) :
    Γ ⊢[PRAAx] Inv a b v (succ j) x := by
  refine (congrMul (prodStep b j x) (.eqRefl _)).eqTrans ?_
  refine (mul_assoc _ _ _).eqTrans ?_
  refine (congrMul (.eqRefl _) hr).eqTrans ?_
  refine Prf.eqTrans ?_ (congrMul (prodStep a j x).eqSymm (.eqRefl _))
  refine Prf.eqTrans ?_ (congrMul hi (.eqRefl (inst2 a j x)) |>.eqTrans ?_)
  · ipra_ring
  · ipra_ring

theorem origin (a b v : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] Inv a b v zero x :=
  (congrMul (prod_zero b x) (.eqRefl _)).eqTrans
    (congrMul (prod_zero a x) (.eqRefl _)).eqSymm

abbrev RecThrough (a b v : PTm 2) (N x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ RecStep a b v (var 0) (Syn.shift x))

theorem telescope (a b v : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] RecThrough a b v N x) :
    Γ ⊢[PRAAx] Inv a b v N x := by
  have hall : Γ ⊢[PRAAx] Fm.all
      (le (var 0) (Syn.shift N) ⟶ Inv a b v (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, trivial⟩ ?_ ?_
    · simp only [Inv, prod, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2,
        PTm.subst_mul, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        LeanProofs.ConciseIPRA.PTm.subst_zero]
      exact .impI (origin a b v x)
    · simp only [Inv, prod, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2,
        PTm.subst_mul, subst_inst2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        LeanProofs.ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have hle : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ Inv a b v (var 0) (Syn.shift x)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
        le_trans (le_succ_self _) Prf.hyp0
      exact advance a b v _ _ (.impE h.allOpen.wk.wk Prf.hyp0) (.impE Prf.hyp1 hle)
  have he := Prf.allE N hall
  simp only [Inv, prod, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2,
    PTm.subst_mul, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    LeanProofs.ConciseIPRA.PTm.subst_zero] at he
  exact .impE he (le_refl N)

theorem exceptional (a b v : PTm 2) (N x last coeff : PTm n)
    (hr : Γ ⊢[PRAAx] RecThrough a b v N x)
    (he : Γ ⊢[PRAAx] last * coeff ≐ inst2 a N x * inst2 v N x) :
    Γ ⊢[PRAAx] prod b N x * (last * coeff) ≐ prod a (succ N) x * inst2 v zero x := by
  refine (congrMul (.eqRefl _) he).eqTrans ?_
  refine Prf.eqTrans ?_ (congrMul (prodStep a N x).eqSymm (.eqRefl _))
  refine Prf.eqTrans ?_ (congrMul (telescope a b v N x hr) (.eqRefl (inst2 a N x)) |>.eqTrans ?_)
  · ipra_ring
  · ipra_ring

def conclusion (a b v : PTm 2) (N x last coeff : PTm n) : Fm PTm n :=
  RecThrough a b v N x ⟶
  (last * coeff ≐ inst2 a N x * inst2 v N x) ⟶
  (prod b N x * (last * coeff) ≐ prod a (succ N) x * inst2 v zero x)

theorem closedExceptional (a b v : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (conclusion a b v (var 0) (var 1) (var 2) (var 3)) := by
  apply closeUniv 4
  exact .impI (.impI (exceptional a b v _ _ _ _ Prf.hyp1 Prf.hyp0))

/-- At positive resonance one, the natural pair (pos, neg) represents
g₁ = pos - neg. The hypothesis is g₁ = (a+b+1) − (a+1)(b+1), obtained
from g = B/h² through degree one. The conclusion is g₁ = −ab. -/
def firstLog (a b pos neg : PTm n) : Fm PTm n :=
  (pos + succ a * succ b ≐ neg + succ (a+b)) ⟶ (pos + a*b ≐ neg)

theorem firstLogSound (a b pos neg : PTm n) :
    Γ ⊢[PRAAx] firstLog a b pos neg := by
  apply Prf.impI
  ipra_lc natEq (Γ := (pos + succ a * succ b ≐ neg + succ (a+b)) :: Γ) Prf.hyp0

theorem closedFirstLog :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (firstLog (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (firstLogSound _ _ _ _)

end LeanProofs.IPRA.Foundations.Transport.ResonanceObject
