import P87ShiftedGuardGraph
import FirstRootBridge
import GuardRank85
import DiophantineConsistency.Compact44.P72Root

/-! Source-only guard positivity and scalar gap. All graph imports are
unelaborated drafts; no rank window or endpoint follows here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.GuardGap87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def eval (e : Expr (Fin 14)) (v : Fin 14 → V) : DiffRing V := e.evalRing (fun j => ι (v j))

/-- The 87 own-zero implies its guard residual is zero. -/
theorem guard_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    eval (P87ShiftedGuard.graph p).guardResidual v=0 := by
  rw [internalZero_iff,P87ShiftedGuard.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : DirectFirstRootModelDraft.fiveSquares (eval (P87ShiftedGuard.graph p).A0 v)
      (eval (P87ShiftedGuard.graph p).A1 v) (eval (P87ShiftedGuard.graph p).aux v-1)
      (eval (P87ShiftedGuard.graph p).gap v) (eval (P87ShiftedGuard.graph p).guardResidual v)=0 := by
    simpa only [DirectFirstRootModelDraft.fiveSquares,eval] using hz
  exact ((DirectFirstRootModelDraft.fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive).2.2.2.2

/-- The 87 literal guard evaluated in the difference ring, with explicit
natural representations for beta and K. -/
theorem guard_eval (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K) :
    eval (P87ShiftedGuard.graph p).guardResidual v =
      (ι (AuxGraphNormClientDraft.q beta v)-ι (v 1)-ι (v 2))*
        (ι (v 6)+ι K*ι (AuxGraphNormClientDraft.q beta v))-ι (v 1)-ι (v 0*beta)*ι (v 13) := by
  simp [eval,P87ShiftedGuard.graph,Expr.evalRing_add,
    Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,
    Expr.evalRing_ofNat,AuxGraphNormClientDraft.q,
    hbeta,hK,map_add,map_mul,map_one] <;> ring

/-- An 87 zero guard forces F+alpha<q, provided F and X are positive and the
beta and K ports have explicit natural model representations. -/
theorem gap_of_87_zero (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hF : 0<v 1) (hw : 0<v 6)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    v 1+v 2<AuxGraphNormClientDraft.q beta v := by
  let q := AuxGraphNormClientDraft.q beta v
  let X := v 6+K*q
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hX : 0<X := by dsimp [X]; exact add_pos_of_pos_of_nonneg hw (Arithmetic.zero_le _)
  have hx : (0 : DiffRing V)<ι X := by
    simpa only [map_zero] using (ι_lt_ι (a := (0:V)) (b := X)).mpr hX
  have hf : (0 : DiffRing V)<ι (v 1) := by
    simpa only [map_zero] using (ι_lt_ι (a := (0:V)) (b := v 1)).mpr hF
  have hb : (0 : DiffRing V)≤ι (v 0*beta)*ι (v 13) := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  have hg := guard_of_zero p v hz
  rw [guard_eval p beta K v hbeta hK] at hg
  have hXcast : ι X=ι (v 6)+ι K*ι q := by simp only [X,map_add,map_mul]
  rw [←hXcast] at hg
  change (ι q-ι (v 1)-ι (v 2))*ι X-ι (v 1)-ι (v 0*beta)*ι (v 13)=0 at hg
  have hp : 0<(ι q-ι (v 1)-ι (v 2))*ι X := by nlinarith
  have hc : 0<(ι q-ι (v 1)-ι (v 2)) := by
    by_contra hn
    have hn' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_of_lt hx)
    exact (not_le_of_gt hp) hn'
  have hlt : ι (v 1+v 2)<ι q := by simp only [map_add]; nlinarith
  exact ι_lt_ι.mp hlt

end DiophantineConsistency.GuardGap87Draft

#print axioms DiophantineConsistency.GuardGap87Draft.gap_of_87_zero
