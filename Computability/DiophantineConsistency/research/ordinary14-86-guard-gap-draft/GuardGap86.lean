import FirstFields86
import GuardRank85
import DiophantineConsistency.Compact44.P72Root

/-! Source-only guard positivity and scalar gap. All graph imports are
unelaborated drafts; no rank window or endpoint follows here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.GuardGap86Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 86 literal guard evaluated in the difference ring, with explicit
natural representations for beta and K. -/
theorem guard_eval (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K) :
    FirstFields86Draft.eval (P86ResidueGraph.graph p).guardResidual v =
      (ι (AuxGraphNormClientDraft.q beta v)-ι (v 1)-ι (v 2))*
        (ι (v 6)+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13) := by
  simp [FirstFields86Draft.eval,P86ResidueGraph.graph,Expr.evalRing_add,
    Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,
    Expr.evalRing_ofNat,AuxGraphNormClientDraft.q,
    hbeta,hK,map_add,map_mul,map_one] <;> ring

/-- An 86 zero guard forces F+alpha<q, provided F and X are positive and the
beta and K ports have explicit natural model representations. -/
theorem gap_of_86_zero (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hF : 0<v 1) (hw : 0<v 6)
    (hz : InternalZero (P86ResidueGraph.graph p).output v) :
    v 1+v 2<AuxGraphNormClientDraft.q beta v := by
  let q := AuxGraphNormClientDraft.q beta v
  let X := v 6
  have hq : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hX : 0<X := hw
  have hx : (0 : DiffRing V)<ι X+ι K := by
    have hxi : (0 : DiffRing V)<ι X := by simpa only [map_zero] using (ι_lt_ι (a := (0:V)) (b := X)).mpr hX
    exact add_pos_of_pos_of_nonneg hxi (ι_nonneg K)
  have hf : (0 : DiffRing V)<ι (v 1) := by
    simpa only [map_zero] using (ι_lt_ι (a := (0:V)) (b := v 1)).mpr hF
  have hb : (0 : DiffRing V)≤ι (v 0*beta)*ι (v 13) := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  have hg := (FirstFields86Draft.fields_of_zero p v hz).2.2.2.2
  rw [guard_eval p beta K v hbeta hK] at hg
  change (ι q-ι (v 1)-ι (v 2))*(ι X+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13)=0 at hg
  have hp : 0<(ι q-ι (v 1)-ι (v 2))*(ι X+ι K) := by nlinarith
  have hc : 0<(ι q-ι (v 1)-ι (v 2)) := by
    by_contra hn
    have hn' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_of_lt hx)
    exact (not_le_of_gt hp) hn'
  have hlt : ι (v 1+v 2)<ι q := by simp only [map_add]; nlinarith
  exact ι_lt_ι.mp hlt

end DiophantineConsistency.GuardGap86Draft

#print axioms DiophantineConsistency.GuardGap86Draft.gap_of_86_zero
