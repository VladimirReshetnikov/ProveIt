import ZeroFields
import NaturalRank
import DiophantineConsistency.Compact44.P72Root

/-! Source-only guard positivity and scalar gap. All graph imports are
unelaborated drafts; no rank window or endpoint follows here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.GuardRank85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 85 literal guard evaluated in the difference ring, with explicit
natural representations for beta and K. -/
theorem guard_eval (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K) :
    ZeroFields8485Draft.eval (P85QcubeGraph.graph p).guardResidual v =
      (ι (AuxGraphNormClientDraft.q beta v)-ι (v 1)-ι (v 2))*
        (ι (v 6)+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13) := by
  simp [ZeroFields8485Draft.eval,P85QcubeGraph.graph,Expr.evalRing_add,
    Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,
    Expr.evalRing_ofNat,AuxGraphNormClientDraft.q,
    hbeta,hK,map_add,map_mul,map_one] <;> ring

/-- An 85 zero guard forces F+alpha<q, provided F and X are positive and the
beta and K ports have explicit natural model representations. -/
theorem gap_of_85_zero (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hF : 0<v 1) (hw : 0<v 6)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
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
  have hg := (ZeroFields8485Draft.fields85 p v hz).2.2.2.2
  rw [guard_eval p beta K v hbeta hK] at hg
  change (ι q-ι (v 1)-ι (v 2))*(ι X+ι K)-ι (v 1)-ι (v 0*beta)*ι (v 13)=0 at hg
  have hp : 0<(ι q-ι (v 1)-ι (v 2))*(ι X+ι K) := by nlinarith
  have hc : 0<(ι q-ι (v 1)-ι (v 2)) := by
    by_contra hn
    have hn' := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (le_of_lt hx)
    exact (not_le_of_gt hp) hn'
  have hlt : ι (v 1+v 2)<ι q := by simp only [map_add]; nlinarith
  exact ι_lt_ι.mp hlt

/-- The same own-zero scalar gap justifies both subtraction casts and the
natural signed-rank representation; no 84 graph zero is assumed. -/
theorem rank_of_85_zero (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hFpos : 0<v 1) (hX : 0<v 6)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    AuxGraphNormClientDraft.rank p beta v=ι (NaturalRank84Draft.naturalRank beta MC MF v) := by
  let q := AuxGraphNormClientDraft.q beta v
  have hgap : v 1+v 2<q := gap_of_85_zero p beta K v hbeta hK hFpos hX hz
  have hF : v 1≤q := le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le (v 2))) hgap)
  have hq0 : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hq : 1≤q := pos_iff_one_le.mp hq0
  have hq2 : 1≤q*q := le_trans hq (le_mul_of_one_le_right (Arithmetic.zero_le q) hq)
  exact NaturalRank84Draft.rank_repr p beta MC MF v hMC hMF hF hq2

end DiophantineConsistency.GuardRank85Draft

#print axioms DiophantineConsistency.GuardRank85Draft.gap_of_85_zero
#print axioms DiophantineConsistency.GuardRank85Draft.rank_of_85_zero
