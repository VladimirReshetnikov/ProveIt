import DiophantineConsistency.ModelBFreshPrivate
import Model69RetainedNorm
import Model69CurrentOuter
import Model69CurrentPhase

/-! Experimental arithmetic-to-ring transfer of the two fresh private norms.
It does not yet construct the fixed-port graph solution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69FreshNorms
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ModelDifferenceRing
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ObjectCurrentEquation2011
open ArithmeticPellRecurrence
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fresh_ring_norms (D b c R G f i T u y m : V)
    (hstrong : f*f=1+D*(b*i*c*c)*(b*i*c*c))
    (hliteral : f*f*c*T=u+c+f*f*R)
    (haux : (D*(b*i*c*c))*(D*(b*i*c*c))*u*u+y*y=
      1+(D*(b*i*c*c))*(D*(b*i*c*c))*y*y)
    (hcarrier : -(ι y : DiffRing V)=1+4*(ι b*(ι m-(ι u)^2*ι G)-ι G)) :
    let S := ι D * (ι b * ι i * (ι c)^2)
    let W := (ι f)^2 * (ι c*ι T-ι R)-ι c
    let Y := 1+4*(ι b*(ι m-W^2*ι G)-ι G)
    (ι f)^2 - ι D*(ι b*ι i*(ι c)^2)^2=1 ∧
    S^2*(W^2-Y^2)+Y^2=1 := by
  dsimp only
  have hw : (ι f)^2*(ι c*ι T-ι R)-ι c=(ι u : DiffRing V) := by
    have h := congrArg (ι : V → DiffRing V) hliteral
    simp only [map_add,map_mul] at h
    linear_combination h
  have hy : 1+4*(ι b*(ι m-((ι f)^2*(ι c*ι T-ι R)-ι c)^2*ι G)-ι G) =
      -(ι y : DiffRing V) := by rw [hw]; exact hcarrier.symm
  have hs := congrArg (ι : V → DiffRing V) hstrong
  have ha := congrArg (ι : V → DiffRing V) haux
  simp only [map_add,map_mul,map_one] at hs ha
  constructor
  · linear_combination hs
  · rw [hy,hw]
    linear_combination ha
/-- Conditional graph zero from the retained and fresh norm data, with all
natural-to-ring outer identifications stated explicitly. -/
theorem graph_zero_of_fresh (p : Fin 4 → V) (v : Fin 14 → V)
    (D b c R G f i T u y m : V)
    (hb : p 0*v 0=b)
    (hc : (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).c=ι c)
    (hD : (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).delta=ι D)
    (hR : (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).rank=ι R)
    (hG : Model69GraphCutDraft.transport (fun j => ι (p j)) (fun j => ι (v j))=ι G)
    (hP : (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).P=1)
    (hQ : (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).Q=1)
    (hstrong : f*f=1+D*(b*i*c*c)*(b*i*c*c))
    (hliteral : f*f*c*T=u+c+f*f*R)
    (haux : (D*(b*i*c*c))*(D*(b*i*c*c))*u*u+y*y=
      1+(D*(b*i*c*c))*(D*(b*i*c*c))*y*y)
    (hcarrier : -(ι y : DiffRing V)=1+4*(ι b*(ι m-(ι u)^2*ι G)-ι G)) :
    DiophantineConsistency.ThirteenCarrier.value69 (fun j => ι (p j))
      (Model69GraphCutDraft.replace (fun j => ι (v j)) (ι f) (ι i) (ι T) (ι m))=0 := by
  have hbr : (ι (p 0) : DiffRing V)*ι (v 0)=ι b := by rw [←map_mul,hb]
  have hn := fresh_ring_norms D b c R G f i T u y m hstrong hliteral haux hcarrier
  apply Model69GraphCutDraft.replace_zero69 _ _ _ _ _ _ hP hQ
  · rw [hD,hc,hbr]
    exact hn.1
  · dsimp only
    rw [hD,hc,hR,hG,hbr]
    exact hn.2

/-- The retained coordinate, discriminant, and transport in the graph view,
under explicit beta and K port equalities and the actual-zero bounds. -/
theorem current_view_fields (p : Fin 4 → V) (v : Fin 14 → V) (G : V)
    (hp0 : p 0=(CurrentMasks2011.beta:V))
    (hp1 : p 1=(CurrentKernel2011.K:V))
    (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v)
    (htrans : ((CurrentKernel2011.K:V)+v 8)*(q v-v 1-v 2)=v 1+G) :
    (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).c =
      ι ((v 10+v 11)*Y v+v 10) ∧
    (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).delta =
      ι (delta (X v*Y v+Y v)) ∧
    Model69GraphCutDraft.transport (fun j => ι (p j)) (fun j => ι (v j))=ι G := by
  have hb := Model69RetainedNorm.current_bounds_for_map v hv hz
  have hgap := Model69ViewMap.map_gap (q v) (v 1) (v 2) hb.1 hb.2.1
  have hC : (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).C =
      ι (q v-v 1-v 2) := by
    simpa only [Model69GraphCutDraft.parentView, hp0, q, map_add, map_mul, map_one] using hgap
  have he := congrArg (ι : V → DiffRing V) htrans
  simp only [map_add,map_mul] at he
  constructor
  · simp only [Model69GraphCutDraft.parentView, hp0, q, Y, map_add, map_mul, map_pow, map_one]
  constructor
  · simp only [Model69GraphCutDraft.parentView, hp0, delta, X, Y, q,
      map_add, map_mul, map_pow, map_one, map_ofNat]
    ring
  · dsimp only [Model69GraphCutDraft.transport]
    rw [hC, hp1]
    linear_combination he

/-- Replace four private coordinates while keeping all nine outer coordinates. -/
def replaceNat (v : Fin 14 → V) (f i T m : V) (j : Fin 13) : V :=
  match j.val with
  | 0 => v 0 | 1 => v 1 | 2 => v 2 | 3 => f | 4 => i | 5 => T
  | 6 => v 7 | 7 => v 8 | 8 => v 9 | 9 => v 10 | 10 => v 11
  | 11 => m | _ => v 13

theorem replaceNat_map (v : Fin 14 → V) (f i T m : V) :
    (fun j => ι (replaceNat v f i T m j)) =
      Model69GraphCutDraft.replace (fun j => ι (v j)) (ι f) (ι i) (ι T) (ι m) := by
  funext j
  fin_cases j <;> rfl

theorem replaceNat_pos (v : Fin 14 → V) (hv : ∀j,0<v j) (f i T m : V)
    (hf : 0<f) (hi : 0<i) (hT : 0<T) (hm : 0<m) :
    ∀j,0<replaceNat v f i T m j := by
  intro j
  fin_cases j <;> first | exact hv _ | exact hf | exact hi | exact hT | exact hm

/-- Actual positive current zero yields a positive 13-coordinate graph zero,
for symbolic ports satisfying all four explicit current-2011 equalities. -/
theorem current_positive_graph_zero (p : Fin 4 → V) (v : Fin 14 → V)
    (hp0 : p 0=(CurrentMasks2011.beta:V))
    (hp1 : p 1=(CurrentKernel2011.K:V))
    (hp2 : p 2=(CurrentMasks2011.lowPort:V))
    (hp3 : p 3=((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))
    (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    ∃ w : Fin 13 → V, (∀j,0<w j) ∧
      DiophantineConsistency.ThirteenCarrier.value69 (fun j => ι (p j)) (fun j => ι (w j))=0 := by
  obtain ⟨L,G,hL,hR,hC,hG,hdiv,htrans,hc⟩ := Model69CurrentOuter.current_outer v hv hz
  have hphase := Model69CurrentPhase.current_rank_phase v hv hz
  let a:=X v*Y v+Y v
  let c:=ycoord (rank v) a
  let b:=(CurrentMasks2011.beta:V)*v 0
  have hb0 : (0:V)<(CurrentMasks2011.beta:V) := by
    have hb := (current_bounds (V:=V)).1
    exact lt_of_lt_of_le (by simp) hb
  have hb : 0<b := mul_pos hb0 (hv 0)
  obtain ⟨f,i,T,u,y,m,hf,hi,hT,hu,hy,hm,hstrong,hyy,hxu,huq,huc,hliteral,haux,hcarrier⟩ :=
    ModelBFreshPrivate.fresh_private a (rank v) b G hb hphase hG hdiv
  obtain ⟨hviewc,hviewD,hviewG⟩ := current_view_fields p v G hp0 hp1 hv hz htrans
  have hc' : (Model69GraphCutDraft.parentView (fun j => ι (p j)) (fun j => ι (v j))).c=ι c := by
    rw [hviewc,hc]
  have hr := Model69RetainedNorm.current_view_rank p v hp0 hp2 hp3 hv hz
  obtain ⟨hP,hQ⟩ := Model69RetainedNorm.current_graph_norms p v hp0 hp2 hp3 hv hz
  have hpb : p 0*v 0=b := by rw [hp0]
  have hzero := graph_zero_of_fresh p v (delta a) b c (rank v) G f i T u y m
    hpb hc' hviewD hr hviewG hP hQ hstrong hliteral haux hcarrier
  refine ⟨replaceNat v f i T m,replaceNat_pos v hv f i T m hf hi hT hm,?_⟩
  rw [replaceNat_map]
  exact hzero

end Model69FreshNorms
#print axioms Model69FreshNorms.fresh_ring_norms
#print axioms Model69FreshNorms.graph_zero_of_fresh
#print axioms Model69FreshNorms.current_view_fields
#print axioms Model69FreshNorms.current_positive_graph_zero
