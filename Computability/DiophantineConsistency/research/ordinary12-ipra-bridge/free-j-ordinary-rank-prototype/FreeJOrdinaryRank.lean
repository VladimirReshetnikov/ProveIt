import DiophantineConsistency.FreeJGraphAuxiliary
import DiophantineConsistency.ArithmeticPellIntegralSolution
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJOrdinaryRank
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellIntegralSolution
open DiophantineConsistency.Ordinary12FreeJ
open FreeJIndexComparison FreeJEarlySize FreeJOrdinaryTransport FreeJGraphAuxiliary
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_ordinary_rank (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
    let z := ev (parts (fun j => (p j:ℤ))).z
    let n := ev (parts (fun j => (p j:ℤ))).n
    let w := n+z
    let c := v 8+v 6*(v 8+v 9)
    let a := v 5*v 6+v 6
    let f := 1+v 3
    let Q := delta a*(f*f-1)
    ∃ (i0 : DiffRing V) (i Z y pi m : V),
      (0 < i) ∧ ((ι i=i0) ∨ (ι i= -i0)) ∧
      ((i*c*c)*(i*c*c)=Q) ∧ (c<Z) ∧ (z=ι Z) ∧ (0<y) ∧
      ((w-i0=ι y) ∨ (w-i0= -ι y)) ∧ Q*(Z*Z)=(Q-1)*(y*y)+1 ∧
      (0<pi) ∧ c=ycoord pi a ∧ (0<m) ∧ pi∣m ∧
      f=xcoord m a ∧ i*c*c=delta a*ycoord m a := by
  let ports : Fin 4 → ℤ := fun j => (p j:ℤ)
  let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
  let z := ev (parts ports).z
  let n := ev (parts ports).n
  let w := n+z
  let c := v 8+v 6*(v 8+v 9)
  let a := v 5*v 6+v 6
  let f := 1+v 3
  let Q := delta a*(f*f-1)
  have hdelta : (3+4*a)+a*a=delta a := by dsimp [delta]; ring
  obtain ⟨i0,i,Z,y,hipos,hisign,_,hstrong,hcZ,hzval,hypos,hysign,haux⟩ :=
    graph_positive_auxiliary p v hb hl hh hv hz
  have hstrong' : (i*c*c)*(i*c*c)=Q := by
    change (i*c*c)*(i*c*c)=((3+4*a)+a*a)*(f*f-1) at hstrong
    dsimp only [Q]
    rw [←hdelta]
    exact hstrong
  have haux' : Q*(Z*Z)=(Q-1)*(y*y)+1 := by
    change (((3+4*a)+a*a)*(f*f-1))*(Z*Z)=
      ((((3+4*a)+a*a)*(f*f-1))-1)*(y*y)+1 at haux
    dsimp only [Q]
    rw [←hdelta]
    exact haux
  obtain ⟨first,main,j,pi,hfirst,hmain,hj13,hjpi,hpi14,hhalf,hroot,horient,hjx,hjy,hpx,hpy,hmod⟩ :=
    comparison p v hb hl hh hv hz
  have hpi : 0<pi := lt_of_lt_of_le (by simp : (0:V)<14) hpi14
  have hcp : c=ycoord pi a := hpy.symm
  have hbig : (a+2)*delta a*delta a<c := (early_size p v hb hl hh hv hz).1
  have hf : 0<f := by dsimp [f]; simp
  obtain ⟨m,hm,hpm,hfm,him⟩ := integral_solution_tsub a c pi i f hpi hipos hf hcp hstrong' hbig
  exact ⟨i0,i,Z,y,pi,m,hipos,hisign,hstrong',hcZ,hzval,hypos,hysign,haux',hpi,hcp,hm,hpm,hfm,him⟩
end FreeJOrdinaryRank
#print axioms FreeJOrdinaryRank.graph_ordinary_rank
