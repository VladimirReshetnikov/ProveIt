import DiophantineConsistency.ArithmeticPellFirstIndex
import DiophantineConsistency.ModelDifferenceRing

/-! UNCOMPILED RESEARCH DRAFT. No declarations here are checked results.
The model theorem derives scalar and first-index windows from the actual
maintained equations; the separate ordered-ring lemmas derive the five sign
consequences from explicit intermediate bounds. The bridge between them,
including natural subtraction and port casts, remains an obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellFirstIndex

section ModelWindows
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The maintained strong norm forces the positive natural `f` above one.
This supplies the discrete `f≥2` input used by the ordered-ring lemma. -/
theorem strong_norm_f_ge_two (a c f i : V)
    (hc : 0<c) (hf : 0<f) (hi : 0<i)
    (hstrict : f*f=1+delta a*(i*c*c)*(i*c*c)) : 2≤f := by
  have hd : 0<delta a := by
    unfold delta
    exact mul_pos (by simp) (by simp)
  have hI : 0<i*c*c := mul_pos (mul_pos hi hc) hc
  have hp : 0<delta a*(i*c*c)*(i*c*c) := mul_pos (mul_pos hd hI) hI
  have hfprod : 1<f*f := by rw [hstrict]; exact lt_add_of_pos_right 1 hp
  have hone : 1≤f := pos_iff_one_le.mp hf
  have hgt : 1<f := by
    by_contra hn
    have he : f=1 := le_antisymm (le_of_not_gt hn) hone
    rw [he] at hfprod
    simpa using hfprod
  simpa using lt_iff_succ_le.mp hgt

/-- Proposed direct application of the *maintained* first-index theorem.
`i` is the original source index, not the scaled index required by the
different `ordinary_first_indices` theorem. All its hypotheses are explicit. -/
theorem windows_from_maintained_norms
    (beta K MC MF J F alpha z f i T s w N eta zeta y gamma : V)
    (hbeta : 0<beta) (hMC : MC<beta) (hMF : MF<2*beta)
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha) (hz : 0<z)
    (hf : 0<f) (hi : 0<i) (hT : 0<T) (hs : 0<s) (hw : 0<w)
    (hN : 0<N) (heta : 0<eta) (hzeta : 0<zeta) (hy : 0<y) (hgamma : 0<gamma) :
    let q:=beta*J+1
    let X:=w*q
    let Y:=s*q^3
    let E:=X*Y
    let k:=eta+zeta
    let c:=k*Y+eta
    let a:=E+Y
    let d:=X+a*c+gamma*(4*a+3)
    let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
    let tau:=E*N+k-R
    let I:=delta a*i*c*c
    let u:=absdiff (f*f*c*T) (f*f*R+c)
    (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 →
    tau*tau=1+(E*Y)*(E*Y+1)*k*k →
    d*d=1+delta a*c*c →
    f*f=1+delta a*(i*c*c)*(i*c*c) →
    I*I*u*u+y*y=1+I*I*y*y →
    0<q-F-alpha ∧ R+2<E ∧ 2*R<c := by
  dsimp only
  intro htransport hfirst hmain hstrict haux
  let q:=beta*J+1
  let E:=(w*q)*(s*q^3)
  let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  let c:=(eta+zeta)*(s*q^3)+eta
  obtain ⟨hgap, _, hRsmall⟩ := scalar_window q beta K MC MF J F alpha z w s
    hbeta hJ hF halpha hz hw hs hMC hMF rfl htransport
  have hE : w*s*q^4=E := by dsimp [E]; ring
  rw [hE] at hRsmall
  obtain ⟨n,h,hn5,hnR,hnrel,htau,hk,hd,hc,hbig,hhalf,hpos,hfinal⟩ :=
    maintained_first_indices beta K MC MF J F alpha z f i T s w N eta zeta y gamma
      hbeta hMC hMF hJ hF halpha hz hf hi hT hs hw hN heta hzeta hy hgamma
      htransport hfirst hmain hstrict haux
  exact ⟨hgap,hRsmall,hhalf⟩
end ModelWindows

section OrderedRing
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The transport window and `R<E` force the first two cut signs. -/
theorem gap_tau_signs (q F alpha E N k r : R)
    (hq : 1≤q) (halpha : 0≤alpha) (hgap : F+alpha≤q)
    (hE : 0≤E) (hN : 1≤N) (hk : 0≤k) (hr : r≤E) :
    0≤(q-1)*(q-F)+alpha ∧ 0≤E*N+k-r := by
  have ha : 0≤q-F := by linarith
  have hb : 0≤(q-1)*(q-F) := mul_nonneg (sub_nonneg.mpr hq) ha
  have hc : 0≤E*(N-1) := mul_nonneg hE (sub_nonneg.mpr hN)
  constructor <;> nlinarith

/-- Bounds derived from the first-index and strong norms force the next two
cut signs. The discrete step `f≥2` is supplied by the natural-model lemma. -/
theorem inner_V_signs (c T r f : R)
    (hc : 0<c) (hT : 1≤T) (hhalf : 2*r<c) (hf : 2≤f) :
    0≤c*T-r ∧ 0≤f*f*(c*T-r)-c := by
  have hct : 0≤c*(T-1) := mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hT)
  have hu : 0<c*T-r := by nlinarith
  have htwo : 0<2*(c*T-r)-c := by nlinarith
  have hf2 : 4≤f*f := by nlinarith [sq_nonneg (f-2)]
  have hprod : 0≤(f*f-4)*(c*T-r) := mul_nonneg (sub_nonneg.mpr hf2) (le_of_lt hu)
  constructor <;> nlinarith

/-- The auxiliary unit norm forces its squared-ordinate difference nonpositive. -/
theorem auxiliary_difference_sign (S V y : R)
    (hS : 0<S) (hy : 1≤y)
    (haux : S*S*(V*V-y*y)+y*y=1) : V*V-y*y≤0 := by
  have hy2 : 1≤y*y := by nlinarith [sq_nonneg (y-1)]
  by_contra h
  have hd : 0<V*V-y*y := lt_of_not_ge h
  have hp : 0<S*S*(V*V-y*y) := mul_pos (mul_pos hS hS) hd
  linarith
end OrderedRing
end DiophantineConsistency.Sign33Draft
