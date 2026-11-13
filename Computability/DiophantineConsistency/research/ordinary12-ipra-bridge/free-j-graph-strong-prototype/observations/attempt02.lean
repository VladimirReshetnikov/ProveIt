import DiophantineConsistency.FreeJGraphIntegrality
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJGraphStrong
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.Ordinary12FreeJ
open FreeJGraphVBound FreeJDenominator FreeJOrdinaryTransport FreeJCurrentDenominator FreeJGraphIntegrality
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_multiplier (p : Fin 4 → ℕ) (v : Fin 12 → V)
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
    ∃ i0 : DiffRing V, A=D*i0 ∧ d*i0*i0=q := by
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
  let Y := w*D-A
  have hdiv := graph_denominator_divides p v hb hl hh hv hz
  change D∣Y at hdiv
  have hwdiv : D∣w*D := ⟨w,by ring⟩
  have hAdiv : D∣A := by
    have hh' := dvd_sub hwdiv hdiv
    have hident : w*D-Y=A := by dsimp only [Y]; ring
    simpa only [hident] using hh'
  obtain ⟨i0,hi⟩ := hAdiv
  have hD : D≠0 := (auxiliary_with_nonzero_denominator p v hb hl hh hv hz).1
  have hdne : d≠0 := by
    intro hzero
    apply hD
    dsimp only [D]
    rw [hzero,zero_mul]
  have hbne : b≠0 := by
    intro hzero
    apply hD
    dsimp only [D]
    rw [hzero,mul_zero]
  have hnorm := actual_unpolarized_zero ports v hz
  change A*A-d*q*b*b=0 at hnorm
  rw [hi] at hnorm
  have hprod : d*b*b*(d*i0*i0-q)=0 := by
    calc
      _=(d*b*i0)*(d*b*i0)-d*q*b*b := by ring
      _=0 := by simpa only [D] using hnorm
  have hnzero : d*b*b≠0 := mul_ne_zero (mul_ne_zero hdne hbne) hbne
  have heq := (mul_eq_zero.mp hprod).resolve_left hnzero
  exact ⟨i0,hi,sub_eq_zero.mp heq⟩
theorem graph_positive_strong (p : Fin 4 → ℕ) (v : Fin 12 → V)
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
    ∃ (i0 : DiffRing V) (i : V), (0 < i) ∧ ((ι i = i0) ∨ (ι i = -i0)) ∧ (A = D*i0) ∧
      ((i*c*c)*(i*c*c)=delta*(f*f-1)) := by
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
  have hqshape : (parts ports).q=graphQ := by rfl
  have hqval : q=ι Q := by
    dsimp only [q,ev]
    rw [hqshape]
    exact graphQ_eval v
  have hdshape : (parts ports).d=(graphC*graphC)*(graphC*graphC) := by rfl
  have hce : graphC.evalRing (fun i => ι (v i))=ι c := by
    simp [graphC,c,Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_var,map_add,map_mul]
  have hdval : d=ι ((c*c)*(c*c)) := by
    dsimp only [d,ev]
    rw [hdshape]
    simp only [Expr.evalRing_mul,hce,map_mul]
  obtain ⟨i0,hA,hn⟩ := graph_signed_multiplier p v hb hl hh hv hz
  change A=D*i0 at hA
  change d*i0*i0=q at hn
  have hQ : 1<Q := Q_gt_one v (hv 3)
  have hQpos : 0<Q := lt_trans (by simp : (0:V)<1) hQ
  have hqne : q≠0 := by
    rw [hqval]
    intro hh0
    have h0 : Q=0 := ι_injective (by simpa using hh0)
    exact (ne_of_gt hQpos) h0
  have hi0ne : i0≠0 := by
    intro hi0
    apply hqne
    rw [←hn,hi0]
    ring
  obtain ⟨i,hisign⟩ := nonneg_or_nonpos i0
  have hipos : 0<i := by
    by_contra hi
    have hi0 : i=0 := le_antisymm (le_of_not_gt hi) (Arithmetic.zero_le i)
    apply hi0ne
    rcases hisign with he | he <;> simpa only [hi0,map_zero,neg_zero] using he
  have hisq : i0*i0=ι i*ι i := by
    rcases hisign with he | he
    · rw [he]
    · rw [he]; ring
  have hstrong : (i*c*c)*(i*c*c)=Q := by
    apply ι_injective
    simp only [map_mul]
    calc
      (ι i*ι c*ι c)*(ι i*ι c*ι c)=(ι ((c*c)*(c*c)))*(ι i*ι i) := by simp only [map_mul]; ring
      _=d*i0*i0 := by rw [hdval,hisq]; ring
      _=q := hn
      _=ι Q := hqval
  refine ⟨i0,i,hipos,?_,hA,?_⟩
  · rcases hisign with he | he
    · exact Or.inl he.symm
    · right
      rw [he]; simp
  · exact hstrong

end FreeJGraphStrong
#print axioms FreeJGraphStrong.graph_signed_multiplier

#print axioms FreeJGraphStrong.graph_positive_strong
