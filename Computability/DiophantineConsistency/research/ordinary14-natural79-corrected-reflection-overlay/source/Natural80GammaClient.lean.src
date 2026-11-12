import Natural80MainPairs
import GammaPremises
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
import DiophantineConsistency.Compact44.DirectMainNorm

/-! Source-only proposed composition from an 80 zero to gamma positivity.
All graph, port, pair, coercion and proof dependencies remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural80GammaClientDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open FirstFactor74Draft Natural80Partial74Draft Natural80JPosDraft
open Natural80OwnZeroNormDraft Natural80GuardGapDraft Natural80MainPairsDraft
open GammaZeroNarrowDraft GammaPremisesDraft DirectMainNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Elementary radix bounds with only beta, J, w and s positive. -/
theorem radix_bounds (beta : V) (u : Fin 14 → V)
    (hb : 0<beta) (hJ : 0<u 0) (hw : 0<u 6) (hs : 0<u 7) :
    2≤q beta u ∧ q beta u≤X beta u ∧ (q beta u)^3≤Y beta u ∧
      8≤Y beta u ∧ 0<scale beta u := by
  have hbJ : 1≤u 0*beta := pos_iff_one_le.mp (mul_pos hJ hb)
  have hq2 : 2≤q beta u := by dsimp [q]; nlinarith
  have hqpos : 0<q beta u := lt_of_lt_of_le (by simp : (0:V)<2) hq2
  have hw1 : 1≤u 6 := pos_iff_one_le.mp hw
  have hs1 : 1≤u 7 := pos_iff_one_le.mp hs
  have hX : q beta u≤X beta u := by
    dsimp [X]
    exact le_mul_of_one_le_right (by simp) hw1
  have hY : (q beta u)^3≤Y beta u := calc
    (q beta u)^3=q beta u*(q beta u*q beta u) := by ring
    _≤(q beta u*(q beta u*q beta u))*u 7 := le_mul_of_one_le_right (by simp) hs1
    _=Y beta u := rfl
  have hq3 : (8:V)≤(q beta u)^3 := by
    have h := pow_le_pow_left₀ (show (0:V)≤2 by simp) hq2 3
    simpa using h
  have hY8 : 8≤Y beta u := le_trans hq3 hY
  have hU : 0<scale beta u := by
    dsimp [scale]
    exact mul_pos (lt_of_lt_of_le (by simp : (0:V)<8) hY8) (mul_pos hqpos hqpos)
  exact ⟨hq2,hX,hY,hY8,hU⟩

/-- Proposed gamma positivity. Every symbolic port representation and
rank-window bound is explicit; gamma itself is not assumed positive. -/
theorem gamma_pos_of_80_zero (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hb : 0<beta) (hKpos : 0<K) (hMCbound : MC<beta) (hMFbound : MF<2*beta)
    (hz : InternalZero (P80NaturalForcedGamma.graph p).output v) : 0<v 12 := by
  let u := partial74 v
  have hJ0 := Natural80JPosDraft.J_pos_of_zero p K v hK hKpos hz
  have hJ : 0<u 0 := by simpa [u,partial74] using hJ0
  have hF : 0<u 1 := by simp [u,partial74]
  have ha : 0<u 2 := by simp [u,partial74]
  have hw : 0<u 6 := by simp [u,partial74]
  have hs : 0<u 7 := by simp [u,partial74]
  have heta : 0<u 9 := by simp [u,partial74]
  have hzeta : 0<u 10 := by simp [u,partial74]
  have hk : 0<k u := by dsimp [k]; exact add_pos heta hzeta
  have hm2 : 2≤m beta u := m_at_least_two beta u hb hJ hw hs
  have hm : 0<m beta u := lt_of_lt_of_le (by simp : (0:V)<2) hm2
  obtain ⟨hq2,hX,hY,hY8,hU⟩ := radix_bounds beta u hb hJ hw hs
  have hgap : u 1+u 2<q beta u := gap_of_80_zero p beta K v hbeta hK hb hKpos hz
  have hunits := units_of_80_zero p beta K v hbeta hK hb hKpos hz
  have hfirst : u 8*u 8=1+m beta u*(m beta u+1)*k u*k u := calc
    u 8*u 8=(m beta u*k u)*(m beta u*k u+k u)+1 := hunits.1
    _=1+m beta u*(m beta u+1)*k u*k u := by ring
  have hmainNorm := norm_of_80_zero p beta K MC MF v hbeta hK hMC hMF hb hKpos hz
  have hdirect :
      let a := X beta u*Y beta u+Y beta u
      let c := u 9+Y beta u*k u
      let H := 3+4*a
      let P := scale beta u*(X beta u+a*c)+H*(scale beta u*u 12+rankValue beta MC MF u+1)
      let N := H*k u
      magnitude (P,N)*magnitude (P,N)=scale beta u*scale beta u*(1+(H+a*a)*(c*c)) := by
    simpa [u,scale,coeffA,coeffC,coeffH,rankValue,positivePart,negativePart,rhsValue,k] using hmainNorm
  obtain ⟨d,_,_,hdnorm⟩ := direct_main_orientation (scale beta u) (X beta u) (Y beta u)
    (k u) (u 9) (u 12) (rankValue beta MC MF u) hU hY8 hk hdirect
  have hmain : d*d=1+((X beta u*Y beta u+Y beta u+1)*(X beta u*Y beta u+Y beta u+3))*
      ((u 9+Y beta u*k u)*(u 9+Y beta u*k u)) := by
    dsimp at hdnorm
    calc
      d*d=1+((3+4*(X beta u*Y beta u+Y beta u))+
        (X beta u*Y beta u+Y beta u)*(X beta u*Y beta u+Y beta u))*
        ((u 9+Y beta u*k u)*(u 9+Y beta u*k u)) := hdnorm
      _=1+((X beta u*Y beta u+Y beta u+1)*(X beta u*Y beta u+Y beta u+3))*
        ((u 9+Y beta u*k u)*(u 9+Y beta u*k u)) := by ring
  have hY1 : 1≤Y beta u := le_trans (by simp : (1:V)≤8) hY8
  have hlarge := large_ordinate_of_two_norms (m beta u) (u 8) (k u) (u 9) (u 10)
    (X beta u) (Y beta u) d hm heta hzeta hY1 rfl hfirst hmain
  have hqeq : q beta u=beta*u 0+1 := by dsimp [q]; ring
  have hrank0 := (ArithmeticAdaptiveRankWindow2011.scalar_rank_window
    (q beta u) beta MC MF (u 0) (u 1) (u 2) hb hJ hF ha hMCbound hMFbound hqeq hgap).2
  have hqpred : q beta u-1=u 0*beta := by dsimp [q]; simp [add_comm]
  have hrankEq : rankValue beta MC MF u =
      ((q beta u-1)*(q beta u-u 1)+u 2)*((q beta u)^2-1)+(MC+q beta u*MF)*u 0 := by
    simp [rankValue,hqpred,pow_two] <;> ring
  have hrank : rankValue beta MC MF u+(q beta u)^3+q beta u+1≤(q beta u)^4 := by
    rw [hrankEq]
    exact hrank0
  have hlarge' : 8*(X beta u*Y beta u*Y beta u)+4≤k u := by
    simpa [m] using hlarge
  obtain ⟨hRk,hcX⟩ := narrow_inequalities (q beta u) (X beta u) (Y beta u) (k u)
    (u 9) (rankValue beta MC MF u) hq2 hX hY heta hlarge' hrank
  apply pos_iff_ne_zero.mpr
  intro hgamma
  have hgammaU : u 12=0 := by simpa [u,partial74] using hgamma
  have hnorm0 :
      let a := X beta u*Y beta u+Y beta u
      let c := u 9+Y beta u*k u
      let H := 3+4*a
      let P := scale beta u*(X beta u+a*c)+H*(scale beta u*(0:V)+rankValue beta MC MF u+1)
      let N := H*k u
      magnitude (P,N)*magnitude (P,N)=scale beta u*scale beta u*(1+(H+a*a)*(c*c)) := by
    simpa [hgammaU] using hdirect
  exact gamma_zero_impossible (scale beta u) (X beta u) (Y beta u) (k u) (u 9)
    (rankValue beta MC MF u) hU hY8 hk hRk hcX hnorm0

end DiophantineConsistency.Natural80GammaClientDraft

#print axioms DiophantineConsistency.Natural80GammaClientDraft.radix_bounds
#print axioms DiophantineConsistency.Natural80GammaClientDraft.gamma_pos_of_80_zero
