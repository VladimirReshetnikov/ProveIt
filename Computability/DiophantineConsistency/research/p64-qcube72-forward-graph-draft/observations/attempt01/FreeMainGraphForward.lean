import IndependentYGraphDraft
import FreeMainForward

/-! Unchecked draft: specialize generic free-main positivity to a 76Y zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainGraphForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem actual_gap_positive (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) :
    let w := lift p v
    let z : Fin 14 → DiffRing V := fun i => ι (w i)
    let g := P64Graph.vals (fun j => (p j:ℤ)) z
    0<g.U*z 13-((g.k-g.RR)-1) := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let zw : Fin 14 → DiffRing V := fun i => ι (w i)
  let q : V := (p 0:V)*w 0+1
  let X : V := w 8*q
  let k : V := w 10+w 11
  let c : V := k*w 7+w 10
  let a : V := X*w 7+w 7
  let H : V := 4*a+3
  let R0 : V := ((p 0:V)*w 0*(q-w 1)+w 2)*(q*q-1)+((p 2:V)+q*(p 3:V))*w 0
  let U : V := w 7*w 7
  obtain ⟨_,hm,_,_,hl⟩ := IndependentYGraphDraft.residuals p v hv hz
  have hmain : InternalZero (P64Graph.graph pp).M w := by
    rw [internalZero_iff]
    change (P64QCube76Y.graph pp).M.evalRing z=0 at hm
    rw [IndependentYGraphDraft.main_same pp,←P64QCubeBinding.main pp z,←P64QCubeMap.lift_cast p v] at hm
    exact hm
  have hlt : InternalZero (P64Graph.graph pp).Lt w := by
    rw [internalZero_iff]
    change (P64QCube76Y.graph pp).Lt.evalRing z=0 at hl
    rw [IndependentYGraphDraft.transport_same pp,P64QCube78GraphSplit.transport_same pp,
      ←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hl
    exact hl
  have hwp := P64QCubeMap.lift_pos p v hv
  have hgap := (P64Root.transport p w hwp hlt).1
  have hb : 0<(p 0:V) := by
    by_contra hn
    have he : (p 0:V)=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [he,zero_mul,zero_add] at hgap
    have hone : 1≤w 1+w 2 := pos_iff_one_le.mp (add_pos (hwp 1) (hwp 2))
    exact (not_lt_of_ge hone) hgap
  have hF : w 1≤(p 0:V)*w 0+1 := le_trans (by simp) (le_of_lt hgap)
  have hYdiv : ((p 0:V)*w 0+1)*((p 0:V)*w 0+1)*((p 0:V)*w 0+1) ∣ w 7 := by
    refine ⟨v 7,?_⟩
    simp [w,lift]
  obtain ⟨g,hg,halign⟩ := P64Root.main_root p w hwp hb hF hYdiv hmain
  change g*g=(a*a+H)*(c*c)+1 at hg
  change U*g+H*k=U*(X+a*c)+H*(U*w 13+R0+1) at halign
  have hnorm : (ι g:DiffRing V)*ι g =
      1+(((ι a:DiffRing V)+2)*((ι a:DiffRing V)+2)-1)*((ι c:DiffRing V)*ι c) := by
    have hh := congrArg (fun t : V => (ι t:DiffRing V)) hg
    simp only [map_add,map_mul,map_ofNat,map_one] at hh
    dsimp [H] at hh
    simp only [map_add,map_mul,map_ofNat] at hh
    linear_combination hh
  have hc3 : (3:V)≤c := by
    have hk2 : (2:V)≤w 10+w 11 := by
      simpa [one_add_one_eq_two] using add_le_add (pos_iff_one_le.mp (hwp 10)) (pos_iff_one_le.mp (hwp 11))
    calc
      (3:V)=2*1+1 := by norm_num
      _≤(w 10+w 11)*w 7+w 10 := add_le_add
        (mul_le_mul hk2 (pos_iff_one_le.mp (hwp 7)) (by norm_num) (Arithmetic.zero_le _))
        (pos_iff_one_le.mp (hwp 10))
      _=c := rfl
  have hx0 : X≤a := by
    have hx : X≤X*w 7 := le_mul_of_one_le_right (Arithmetic.zero_le X) (pos_iff_one_le.mp (hwp 7))
    exact le_trans hx (le_add_of_nonneg_right (Arithmetic.zero_le _))
  have hn : (2:DiffRing V)≤(ι a:DiffRing V)+2 := by have hh := ι_nonneg a; linarith
  have hc : (3:DiffRing V)≤ι c := by
    have hh := (ι_le_ι (V:=V)).mpr hc3
    rwa [map_ofNat] at hh
  have hx : (ι X:DiffRing V)≤((ι a:DiffRing V)+2)-2 := by
    have hh := (ι_le_ι (V:=V)).mpr hx0
    linarith
  have hUp : (0:DiffRing V)<ι U := ModelArithmetic.ι_pos (mul_pos (hwp 7) (hwp 7))
  have hHp : (0:DiffRing V)<ι H := ModelArithmetic.ι_pos (by dsimp [H]; simp)
  have hal : (ι U:DiffRing V)*(ι g-(ι X+ι a*ι c)) =
      ι H*(ι U*ι (w 13)-((ι k-ι R0)-1)) := by
    have hh := congrArg (fun t : V => (ι t:DiffRing V)) halign
    simp only [map_add,map_mul,map_one] at hh
    linear_combination hh
  have hpositive := FreeMainForward.positive_of_pell_bound
    ((ι a:DiffRing V)+2) (ι c) (ι g) (ι X) (ι U) (ι H)
    (ι U*ι (w 13)-((ι k-ι R0)-1)) hn hc (ι_nonneg g) hx hUp hHp hnorm (by simpa using hal)
  change 0<(P64Graph.vals pp zw).U*zw 13-(((P64Graph.vals pp zw).k-(P64Graph.vals pp zw).RR)-1)
  rw [P64Root.c_U,P64Root.c_k,P64Root.c_RR p w hF]
  exact hpositive

theorem exists_positive_main_gap (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) :
    ∃h : V, 0<h ∧
      let w := lift p v
      let z : Fin 14 → DiffRing V := fun i => ι (w i)
      let g := P64Graph.vals (fun j => (p j:ℤ)) z
      ι h=g.U*z 13-((g.k-g.RR)-1) := by
  have hp := actual_gap_positive p v hv hz
  obtain ⟨h,hh⟩ := ModelDifferenceRing.nonneg_iff.mp (le_of_lt hp)
  have hpos : 0<h := by
    apply (ι_lt_ι (V:=V)).mp
    rw [map_zero,←hh]
    exact hp
  exact ⟨h,hpos,hh.symm⟩

#print axioms FreeMainGraphForward.actual_gap_positive
#print axioms FreeMainGraphForward.exists_positive_main_gap
end FreeMainGraphForward
