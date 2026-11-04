import DiophantineConsistency.Compact44.FreeJGraphStrong
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJGraphAuxiliary
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.Ordinary12FreeJ
open FreeJGraphVBound FreeJDenominator FreeJOrdinaryTransport FreeJCurrentDenominator
open FreeJGraphIntegrality FreeJGraphStrong
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_positive_auxiliary (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
    let q := ev (parts (fun j => (p j:ℤ))).q
    let d := ev (parts (fun j => (p j:ℤ))).d
    let z := ev (parts (fun j => (p j:ℤ))).z
    let n := ev (parts (fun j => (p j:ℤ))).n
    let w := n+z
    let h := (1-q)*w*w+q*z*z-1
    let b := 2*(1-q)*w
    let A := d*h+q*(1-q)
    let D := d*b
    let c := v 8+v 6*(v 8+v 9)
    let a := v 5*v 6+v 6
    let delta := (3+4*a)+a*a
    let f := 1+v 3
    let Q := delta*(f*f-1)
    ∃ (i0 : DiffRing V) (i Z y : V),
      (0 < i) ∧ ((ι i = i0) ∨ (ι i = -i0)) ∧ (A = D*i0) ∧
      ((i*c*c)*(i*c*c)=Q) ∧ (c < Z) ∧ (z=ι Z) ∧ (0 < y) ∧
      ((w-i0=ι y) ∨ (w-i0= -ι y)) ∧ Q*(Z*Z)=(Q-1)*(y*y)+1 := by
  let ports : Fin 4 → ℤ := fun j => (p j:ℤ)
  let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
  let q := ev (parts ports).q
  let d := ev (parts ports).d
  let z := ev (parts ports).z
  let n := ev (parts ports).n
  let w := n+z
  let h := (1-q)*w*w+q*z*z-1
  let b := 2*(1-q)*w
  let A := d*h+q*(1-q)
  let D := d*b
  let c := v 8+v 6*(v 8+v 9)
  let a := v 5*v 6+v 6
  let delta := (3+4*a)+a*a
  let f := 1+v 3
  let Q := delta*(f*f-1)
  obtain ⟨i0,i,hipos,hisign,hA,hstrong⟩ := graph_positive_strong p v hb hl hh hv hz
  change A=D*i0 at hA
  change (i*c*c)*(i*c*c)=Q at hstrong
  let y0 := w-i0
  let Y := w*D-A
  have hY : Y=D*y0 := by dsimp only [Y,y0]; rw [hA]; ring
  have hgraph := auxiliary_with_nonzero_denominator p v hb hl hh hv hz
  change D≠0 ∧ q*z*z*D*D-(q-1)*Y*Y-D*D=0 at hgraph
  have hfactor : (D*D)*(q*z*z-(q-1)*y0*y0-1)=0 := by
    calc
      _=q*z*z*D*D-(q-1)*Y*Y-D*D := by rw [hY]; ring
      _=0 := hgraph.2
  have hnorm0 : q*z*z-(q-1)*y0*y0-1=0 :=
    (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero hgraph.1 hgraph.1)
  have hnorm : q*z*z=(q-1)*y0*y0+1 := by linarith
  have hqshape : (parts ports).q=graphQ := by rfl
  have hqval : q=ι Q := by
    dsimp only [q,ev]
    rw [hqshape]
    exact graphQ_eval v
  have hQ : 1<Q := Q_gt_one v (hv 3)
  let Zpair := pairEval (graphV ports) v
  have hV := graph_bound p v hb hl hh hv hz
  change 1<c ∧ Zpair.2+c<Zpair.1 at hV
  have hzshape : (parts ports).z=graphV ports := by rfl
  have hzrep : z=ι Zpair.1-ι Zpair.2 := by
    dsimp only [z,ev]
    rw [hzshape]
    have heval := split_evalRing (graphV ports) (fun i => ι (v i))
    rw [←evalSemiring_map,←evalSemiring_map] at heval
    change ι Zpair.1-ι Zpair.2=_ at heval
    exact heval.symm
  have hcZ : ι c<z := by
    rw [hzrep]
    apply lt_sub_iff_add_lt.mpr
    have h := (ι_lt_ι (a:=Zpair.2+c) (b:=Zpair.1)).mpr hV.2
    simpa only [map_add,add_comm] using h
  have hc1 : (1:DiffRing V)<ι c := by
    simpa using (ι_lt_ι (a:=1) (b:=c)).mpr hV.1
  have hz1 : (1:DiffRing V)<z := lt_trans hc1 hcZ
  obtain ⟨Z,hzval⟩ := nonneg_iff.mp (le_of_lt (lt_trans (by simp : (0:DiffRing V)<1) hz1))
  have hcZnat : c<Z := (ι_lt_ι (a:=c) (b:=Z)).mp (by simpa only [←hzval] using hcZ)
  have hq1 : (1:DiffRing V)<q := by
    rw [hqval]
    simpa using (ι_lt_ι (a:=1) (b:=Q)).mpr hQ
  have hzsq : (1:DiffRing V)≤z*z := by
    calc
      1=1*1 := by ring
      _≤z*z := mul_le_mul (le_of_lt hz1) (le_of_lt hz1) (by positivity) (by positivity)
  have hqpos : (0:DiffRing V)<q := lt_trans (by simp) hq1
  have hqz : (1:DiffRing V)<q*z*z := by
    calc
      1<q := hq1
      _=q*1 := by ring
      _≤q*(z*z) := mul_le_mul_of_nonneg_left hzsq (le_of_lt hqpos)
      _=q*z*z := by ring
  have hy0ne : y0≠0 := by
    intro hy0
    have he : q*z*z=1 := by simpa only [hy0,mul_zero,zero_add] using hnorm
    exact (ne_of_gt hqz) he
  have hys : ∃ y : V, y0=ι y ∨ y0= -ι y := by
    rcases nonneg_or_nonpos y0 with ⟨j,hj⟩ | ⟨j,hj⟩
    · exact ⟨j,Or.inl hj⟩
    · exact ⟨j,Or.inr hj⟩
  obtain ⟨y,hysign⟩ := hys
  have hypos : 0 < y := by
    by_contra hy
    have hyzero : y=0 := le_antisymm (le_of_not_gt hy) (Arithmetic.zero_le y)
    apply hy0ne
    rcases hysign with he | he <;> simpa only [hyzero,map_zero,neg_zero] using he
  have hysq : y0*y0=ι y*ι y := by
    rcases hysign with he | he
    · rw [he]
    · rw [he]; ring
  have hQsub : Q-1+1=Q := tsub_add_cancel_of_le (le_of_lt hQ)
  have hQcast : ι (Q-1)+1=ι Q := by
    simpa only [map_add,map_one] using congrArg (fun x : V => ι x) hQsub
  have hqsub : q-1=ι (Q-1) := by
    calc
      q-1=ι Q-1 := by rw [hqval]
      _=(ι (Q-1)+1)-1 := by rw [hQcast]
      _=ι (Q-1) := by ring
  have hnat : Q*(Z*Z)=(Q-1)*(y*y)+1 := by
    apply ι_injective
    simp only [map_add,map_mul,map_one]
    calc
      ι Q*(ι Z*ι Z)=q*z*z := by rw [hqval,hzval]; ring
      _=(q-1)*y0*y0+1 := hnorm
      _=(q-1)*(y0*y0)+1 := by ring
      _=ι (Q-1)*(ι y*ι y)+1 := by rw [hqsub,hysq]
  exact ⟨i0,i,Z,y,hipos,hisign,hA,hstrong,hcZnat,hzval,hypos,hysign,hnat⟩
end FreeJGraphAuxiliary
#print axioms FreeJGraphAuxiliary.graph_positive_auxiliary
