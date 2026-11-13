import DiophantineConsistency.FreeJOrdinaryRank
import DiophantineConsistency.ArithmeticPellResidueAux
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJExactOrdinary
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.ArithmeticGcdNormalization
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellCongruences
open DiophantineConsistency.ArithmeticPellHalfIndex
open DiophantineConsistency.ArithmeticPellResidueAux
open DiophantineConsistency.Ordinary12FreeJ
open FreeJGraphVBound FreeJDenominator FreeJFirstTransport FreeJEarlyWindow
open FreeJIndexComparison FreeJEarlySize FreeJOrdinaryTransport FreeJGraphAuxiliary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exact_ordinary_indices (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let a : V := v 5*v 6+v 6
    let c : V := v 8+v 6*(v 8+v 9)
    ∃ first main j pi : V, 0<first ∧ 0<main ∧ 13≤j ∧ j<pi ∧ pi=R ∧ 2*j=R+1 ∧
      xcoord j (2*((v 5*v 6)*v 6-1)+1)=first ∧
      2*ycoord j (2*((v 5*v 6)*v 6-1)+1)=v 8+v 9 ∧
      xcoord pi a=main ∧ ycoord pi a=c := by
  let ports : Fin 4 → ℤ := fun j => (p j:ℤ)
  let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
  let z := ev (parts ports).z
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let c := v 8+v 6*(v 8+v 9)
  let a := v 5*v 6+v 6
  let f := 1+v 3
  let Q := delta a*(f*f-1)
  have hdelta : (3+4*a)+a*a=delta a := by dsimp [delta]; ring
  obtain ⟨i0,i,Z,y,hipos,hisign,_,hstrong,hcZ,hzval,hypos,hysign,haux⟩ :=
    graph_positive_auxiliary p v hb hl hh hv hz
  have hs : (i*c*c)*(i*c*c)=Q := by
    change (i*c*c)*(i*c*c)=((3+4*a)+a*a)*(f*f-1) at hstrong
    dsimp only [Q]
    rw [←hdelta]
    exact hstrong
  have ha : Q*(Z*Z)=(Q-1)*(y*y)+1 := by
    change (((3+4*a)+a*a)*(f*f-1))*(Z*Z)=
      ((((3+4*a)+a*a)*(f*f-1))-1)*(y*y)+1 at haux
    dsimp only [Q]
    rw [←hdelta]
    exact haux
  obtain ⟨first,main,j,pi,hfirst,hmain,hj13,hjpi,hpi14,hhalf,hroot,horient,hjx,hjy,hpx,hpy,hmod⟩ :=
    comparison p v hb hl hh hv hz
  have hpi : 0<pi := lt_of_lt_of_le (by simp : (0:V)<14) hpi14
  have hc : 0<c := by dsimp [c]; exact add_pos (hv 8) (mul_pos (hv 6) (add_pos (hv 8) (hv 9)))
  have hf : 0<f := by dsimp [f]; simp
  have hq : 0<q := by dsimp [q]; simp
  obtain ⟨hR24,hupper⟩ := early_window p v hb hl hh hv hz
  have hR : 0<R := lt_of_lt_of_le (by simp : (0:V)<24) hR24
  have hRlt : R+1<q^4 := by
    have hp : 0<q^3+q := add_pos (pow_pos hq _) hq
    calc
      R+1<(R+1)+(q^3+q) := lt_add_of_pos_right _ hp
      _=R+q^3+q+1 := by ring
      _≤q^4 := hupper
  have hbig : (a+2)*delta a*delta a<c := (early_size p v hb hl hh hv hz).1
  have hmainnorm : main*main=1+delta a*c*c := calc
    main*main=xcoord pi a*xcoord pi a := by rw [hpx]
    _=1+delta a*ycoord pi a*ycoord pi a := norm pi a
    _=1+delta a*c*c := by rw [hpy]
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp (freej_first_factor_transport p v hb hv hz).2
  have hF : v 1<q := lt_of_le_of_lt (by simp) hgap
  have hRe : Equivalent (pairEval (graphR ports) v) (natural R) := R_eval p v hF
  have hVe := V_eval ports v R hRe
  let zp := pairEval (graphV ports) v
  have hzshape : (parts ports).z=graphV ports := by rfl
  have hzeval : ι zp.1-ι zp.2=ι Z := by
    have he := split_evalRing (graphV ports) (fun j => ι (v j))
    rw [←evalSemiring_map,←evalSemiring_map] at he
    change ι zp.1-ι zp.2=_ at he
    change z=ι Z at hzval
    simpa only [z,ev,hzshape,hzval] using he
  have hzeq : Equivalent zp (natural Z) := by
    have hh' : ι zp.1=ι (zp.2+Z) := by
      rw [map_add]
      linarith [hzeval]
    have hn := ι_injective hh'
    simpa only [Equivalent,natural,add_zero] using hn
  have heq := equivalent_trans (equivalent_symm hzeq) hVe
  have hform : f*f*c*v 4=(f*f*R+c)+Z := by
    change Z+(f*f*R+c)=0+f*f*v 4*c at heq
    calc
      _=f*f*v 4*c := by ring
      _=Z+(f*f*R+c) := by simpa using heq.symm
      _=(f*f*R+c)+Z := by ring
  have hAbs : absdiff (f*f*c*v 4) (f*f*R+c)=Z := by
    simpa only [magnitude,absdiff] using (magnitude_of_add hform)
  have hQ : 1<Q := by
    have hx := Q_gt_one v (hv 3)
    change 1<((3+4*a)+a*a)*(f*f-1) at hx
    dsimp only [Q]
    rw [←hdelta]
    exact hx
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (le_of_lt hQ)
  have hsadd : (i*c*c)*(i*c*c)+delta a=delta a*(f*f) :=
    norm_tsub_to_add (delta a) f (i*c*c) hf hs
  have huf : SignMod f Z c := by
    rw [←hAbs]
    apply absdiff_residue f (f*f*c*v 4) (f*f*R+c) c hf
    rw [show f*f*c*v 4=f*(f*c*v 4) by ring,show f*f*R=f*(f*R) by ring]
    simp only [mod_mul_add' _ _ hf]
  have huc : SignMod c Z R := by
    rw [←hAbs]
    exact signed_residue_of_relaxed_auxiliary a c pi i f (v 4) R hpi hipos hf hc hpy hsadd hbig
  have hauxadd : Q*Z*Z+y*y=1+Q*y*y := by
    calc
      Q*Z*Z+y*y=Q*(Z*Z)+y*y := by ring
      _=((Q-1)*(y*y)+1)+y*y := by rw [ha]
      _=1+(Q-1+1)*(y*y) := by ring
      _=1+Q*y*y := by rw [hQ1]; ring
  have hauxnorm : (i*c*c)*(i*c*c)*Z*Z+y*y=1+(i*c*c)*(i*c*c)*y*y := by
    rw [hs]
    exact hauxadd
  obtain ⟨_,hcR⟩ := half_index a c main f i R y Z hc hipos hf hR hypos hmainnorm hsadd hbig hhalf hauxnorm huf huc
  have hpiR : pi=R := (y_strictMono a).injective (hpy.trans hcR)
  have hjR : j<R := by rwa [←hpiR]
  change (2*j)%(q^4)=R+1 at hmod
  have hsmall : 2*j<q^4+(R+1) := calc
    2*j<2*R := mul_lt_mul_of_pos_left hjR (by simp)
    _<q^4+(R+1) := by
      have hle : R≤R+1 := by simp
      have hlt : R<q^4 := lt_trans (lt_add_one R) hRlt
      simpa only [two_mul,add_assoc] using add_lt_add_of_lt_of_le hlt hle
  have hdiv : (2*j)/(q^4)=0 := by
    by_contra hz'
    have hd : 1≤(2*j)/(q^4) := pos_iff_one_le.mp (pos_iff_ne_zero.mpr hz')
    have he : q^4+(R+1)≤2*j := calc
      q^4+(R+1)≤q^4*((2*j)/(q^4))+(R+1) :=
        _root_.add_le_add (le_mul_of_one_le_right (by simp) hd) (le_refl _)
      _=2*j := by rw [←hmod]; exact div_add_mod _ _
    exact (not_le_of_gt hsmall) he
  have hjR1 : 2*j=R+1 := by
    have he := (div_add_mod (2*j) (q^4)).symm
    rw [hdiv,hmod] at he
    simpa only [mul_zero,zero_add] using he
  exact ⟨first,main,j,pi,hfirst,hmain,hj13,hjpi,hpiR,hjR1,hjx,hjy,hpx,hpy⟩
end FreeJExactOrdinary
#print axioms FreeJExactOrdinary.exact_ordinary_indices
