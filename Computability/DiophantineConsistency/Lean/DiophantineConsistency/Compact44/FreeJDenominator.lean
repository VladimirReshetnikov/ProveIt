import DiophantineConsistency.Compact44.FreeJGraphVBound
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJDenominator
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.Ordinary12FreeJ
open FreeJGraphVBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem Q_eval (v : Fin 12 → V) :
    let a := v 5*v 6+v 6
    let d := (3+4*a)+a*a
    let f := 1+v 3
    Equivalent (pairEval graphQ v) (natural (d*(f*f-1))) := by
  let a := v 5*v 6+v 6
  let d := (3+4*a)+a*a
  let f := 1+v 3
  have hf1 : 1≤f*f := by
    have hf : 1≤f := by dsimp [f]; simp
    calc 1=1*1 := by ring
      _ ≤ f*f := mul_le_mul hf hf (by simp) (by simp)
  have hn : f*f-1+1=f*f := tsub_add_cancel_of_le hf1
  simp [graphQ,pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural,HSub.hSub,Sub.sub]
  have hcalc : d*(f*f)=d+d*(f*f-1) := by
    calc d*(f*f)=d*((f*f-1)+1) := by rw [hn]
      _=d+d*(f*f-1) := by ring
  dsimp only [a,d,f] at hcalc
  simp only [HSub.hSub,Sub.sub] at hcalc
  exact hcalc
theorem Q_gt_one (v : Fin 12 → V) (ht : 0<v 3) :
    let a := v 5*v 6+v 6
    let d := (3+4*a)+a*a
    let f := 1+v 3
    1<d*(f*f-1) := by
  let a := v 5*v 6+v 6
  let d := (3+4*a)+a*a
  let f := 1+v 3
  have hf2 : (2:V)≤f := by
    dsimp [f]
    calc 2=1+1 := by ring
      _ ≤ 1+v 3 := by simpa only [add_comm] using add_le_add_left (pos_iff_one_le.mp ht) (1:V)
  have hf4 : (4:V)≤f*f := by
    calc 4=2*2 := by ring
      _≤f*f := mul_le_mul hf2 hf2 (by simp) (by simp)
  have hfirst : (1:V)≤f*f := le_trans (by simp : (1:V)≤4) hf4
  have heq : f*f-1+1=f*f := tsub_add_cancel_of_le hfirst
  have h3 : (3:V)≤f*f-1 := (add_le_add_iff_right (1:V)).mp (by
    rw [heq]
    have hn : (3:V)+1=4 := by ring
    rw [hn]
    exact hf4)
  have hd : (1:V)≤d := by
    dsimp [d]
    calc 1≤3 := by simp
      _≤3+4*a := by simp
      _≤(3+4*a)+a*a := by simp
  calc
    1<3 := by simp
    _≤1*(f*f-1) := by simpa using h3
    _≤d*(f*f-1) := mul_le_mul_of_nonneg_right hd (by simp)
theorem neg_times_pos (x y : Pair V) (hx : x.1<x.2) (hy : y.2<y.1) :
    (multiply x y).1 < (multiply x y).2 := by
  let a := x.2-x.1
  let b := y.1-y.2
  have ha : 0<a := tsub_pos_iff_lt.mpr hx
  have hb : 0<b := tsub_pos_iff_lt.mpr hy
  have hx' : x.2=x.1+a := by
    dsimp [a]
    rw [add_comm, tsub_add_cancel_of_le (le_of_lt hx)]
  have hy' : y.1=y.2+b := by
    dsimp [b]
    rw [add_comm, tsub_add_cancel_of_le (le_of_lt hy)]
  have eq : (multiply x y).2=(multiply x y).1+a*b := by
    simp only [multiply]
    rw [hx',hy']
    ring
  rw [eq]
  exact lt_add_of_pos_right _ (mul_pos ha hb)

theorem scale_negative (a : V) (x : Pair V) (ha : 0<a) (hx : x.1<x.2) :
    (multiply (natural a) x).1<(multiply (natural a) x).2 := by
  simpa [multiply,natural] using mul_lt_mul_of_pos_left hx ha

theorem one_sub_eval (e : Expr (Fin 12)) (v : Fin 12 → V) :
    pairEval (1-e) v = (1+(pairEval e v).2,(pairEval e v).1) := by
  simp [pairEval,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub]

theorem var_add_eval (e : Expr (Fin 12)) (v : Fin 12 → V) :
    pairEval (.var 10+e) v = (v 10+(pairEval e v).1,(pairEval e v).2) := by
  simp [pairEval,Expr.splitNatural,NatExpr.evalSemiring]

def graphC : Expr (Fin 12) :=
  .var 8+.var 6*(.var 8+.var 9)

def graphB (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  (2*(1-graphQ))*(.var 10+graphV p)

def graphD (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  ((graphC*graphC)*(graphC*graphC))*graphB p

theorem pair_mul (e f : Expr (Fin 12)) (v : Fin 12 → V) :
    pairEval (e*f) v = multiply (pairEval e v) (pairEval f v) := rfl

theorem c4_eval (v : Fin 12 → V) :
    let c := v 8+v 6*(v 8+v 9)
    pairEval ((graphC*graphC)*(graphC*graphC)) v = natural ((c*c)*(c*c)) := by
  simp [graphC,pairEval,Expr.splitNatural,NatExpr.evalSemiring,natural]

theorem two_eval (v : Fin 12 → V) : pairEval (2 : Expr (Fin 12)) v = natural (2:V) := by
  simp [pairEval,Expr.splitNatural,NatExpr.evalSemiring,natural]

theorem denominator_negative (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let z := pairEval (graphD (fun j => (p j:ℤ))) v
    z.1<z.2 := by
  let a := v 5*v 6+v 6
  let delta := (3+4*a)+a*a
  let f := 1+v 3
  let Q := delta*(f*f-1)
  let P := pairEval graphQ v
  let Z := pairEval (graphV (fun j => (p j:ℤ))) v
  let c := v 8+v 6*(v 8+v 9)
  have hQ : 1<Q := Q_gt_one v (hv 3)
  have hQE := Q_eval v
  change Equivalent P (natural Q) at hQE
  have hpeq : P.1=P.2+Q := by simpa [Equivalent,natural] using hQE
  have hneg : (pairEval (1-graphQ) v).1<(pairEval (1-graphQ) v).2 := by
    rw [one_sub_eval]
    change 1+P.2<P.1
    rw [hpeq]
    simpa [add_comm] using add_lt_add_left hQ P.2
  have hZ := graph_bound p v hb hl hh hv hz
  change 1<c ∧ Z.2+c<Z.1 at hZ
  have hpos : (pairEval (.var 10+graphV (fun j => (p j:ℤ))) v).2 <
      (pairEval (.var 10+graphV (fun j => (p j:ℤ))) v).1 := by
    rw [var_add_eval]
    change Z.2<v 10+Z.1
    calc Z.2≤Z.2+c := by simp
      _<Z.1 := hZ.2
      _≤v 10+Z.1 := by simp
  have hc : 0<c := lt_trans (by simp : (0:V)<1) hZ.1
  have hc4 : 0<(c*c)*(c*c) := mul_pos (mul_pos hc hc) (mul_pos hc hc)
  have htwo := scale_negative (2:V) (pairEval (1-graphQ) v) (by simp) hneg
  have hbneg := neg_times_pos (multiply (natural (2:V)) (pairEval (1-graphQ) v))
    (pairEval (.var 10+graphV (fun j => (p j:ℤ))) v) htwo hpos
  have hDneg := scale_negative ((c*c)*(c*c))
    (multiply (multiply (natural (2:V)) (pairEval (1-graphQ) v))
      (pairEval (.var 10+graphV (fun j => (p j:ℤ))) v)) hc4 hbneg
  have hBeq : pairEval (graphB (fun j => (p j:ℤ))) v =
      multiply (multiply (natural (2:V)) (pairEval (1-graphQ) v))
        (pairEval (.var 10+graphV (fun j => (p j:ℤ))) v) := by
    unfold graphB
    rw [pair_mul]
    congr 1
  have hDeq : pairEval (graphD (fun j => (p j:ℤ))) v =
      multiply (natural ((c*c)*(c*c)))
        (multiply (multiply (natural (2:V)) (pairEval (1-graphQ) v))
          (pairEval (.var 10+graphV (fun j => (p j:ℤ))) v)) := by
    unfold graphD
    rw [pair_mul,c4_eval,hBeq]
  change (pairEval (graphD (fun j => (p j:ℤ))) v).1 < _
  rw [hDeq]
  exact hDneg
end FreeJDenominator
#print axioms FreeJDenominator.Q_eval

#print axioms FreeJDenominator.Q_gt_one

#print axioms FreeJDenominator.neg_times_pos
#print axioms FreeJDenominator.scale_negative
#print axioms FreeJDenominator.one_sub_eval
#print axioms FreeJDenominator.var_add_eval

#print axioms FreeJDenominator.denominator_negative
