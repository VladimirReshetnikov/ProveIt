import ZeroFields
import GraphNormClient
import DiophantineConsistency.Compact44.P72Root

/-! Source-only guard positivity and scalar gap. All graph imports are
unelaborated drafts; no rank window or endpoint follows here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.GuardGap84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 84 literal guard evaluated in the difference ring, with explicit
natural representations for beta and K. -/
theorem guard_eval (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K) :
    ZeroFields8485Draft.eval (P84QcubeGraph.graph p).guardResidual v =
      (ι (AuxGraphNormClientDraft.q beta v)-ι (v 1)-ι (v 2))*
        (ι (AuxGraphNormClientDraft.X beta v)+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13) := by
  simp [ZeroFields8485Draft.eval,P84QcubeGraph.graph,Expr.evalRing_add,
    Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,
    Expr.evalRing_ofNat,AuxGraphNormClientDraft.q,AuxGraphNormClientDraft.X,
    hbeta,hK,map_add,map_mul,map_one] <;> ring

/-- A zero guard forces F+alpha<q, provided F and w are positive and the
beta and K ports have explicit natural model representations. -/
theorem gap_of_84_zero (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hF : 0<v 1) (hw : 0<v 6)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    v 1+v 2<AuxGraphNormClientDraft.q beta v := by
  let q := AuxGraphNormClientDraft.q beta v
  let X := AuxGraphNormClientDraft.X beta v
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hX : 0<X := by dsimp [X,AuxGraphNormClientDraft.X]; exact mul_pos hq hw
  have hx : (0 : DiffRing V)<ι X+ι K := by
    have hxi : (0 : DiffRing V)<ι X := by simpa only [map_zero] using (ι_lt_ι (a := (0:V)) (b := X)).mpr hX
    exact add_pos_of_pos_of_nonneg hxi (ι_nonneg K)
  have hf : (0 : DiffRing V)<ι (v 1) := by
    simpa only [map_zero] using (ι_lt_ι (a := (0:V)) (b := v 1)).mpr hF
  have hb : (0 : DiffRing V)≤ι (v 0*beta)*ι (v 13) := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  have hg := (ZeroFields8485Draft.fields84 p v hz).2.2.2.2
  rw [guard_eval p beta K v hbeta hK] at hg
  change (ι q-ι (v 1)-ι (v 2))*(ι X+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13)=0 at hg
  have hp : 0<(ι q-ι (v 1)-ι (v 2))*(ι X+ι K) := by nlinarith
  have hc : 0<(ι q-ι (v 1)-ι (v 2)) := by
    by_contra hn
    have hn' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_of_lt hx)
    exact (not_le_of_gt hp) hn'
  have hlt : ι (v 1+v 2)<ι q := by simp only [map_add]; nlinarith
  exact ι_lt_ι.mp hlt

end DiophantineConsistency.GuardGap84Draft

#print axioms DiophantineConsistency.GuardGap84Draft.gap_of_84_zero
