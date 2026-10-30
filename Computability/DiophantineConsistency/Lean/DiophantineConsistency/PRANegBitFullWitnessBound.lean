import DiophantineConsistency.PRANegExpWitnessBound
import DiophantineConsistency.PRANegLenbitRewritingBound
/-! A polynomial bound for negative Foundation bitDef. The full
    recursive-history and refutation obligations remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegBitFullWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] expDef

def negBitMajorant (y : V) := PRANegExponentialWitnessBound.negExponentialMajorant y+y+1

theorem negBit_bound (x y : V) : (∼bitDef.val).Evalb ![x,y] →
    (bnd (∼bitDef.val)).Evalb ![x,y,negBitMajorant y] := by
  intro h
  simp [bitDef, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs, bnd, bnd_open] at h ⊢
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hy : y ≤ PRANegExponentialWitnessBound.negExponentialMajorant y+y := le_add_self
  have hyw : y+1 ≤ negBitMajorant y := by simpa [negBitMajorant,add_comm] using add_le_add_right hy 1
  intro z
  by_cases hz : y+1 ≤ z
  · exact Or.inl hz
  · have hzy : z ≤ y := lt_succ_iff_le.mp (lt_of_not_ge hz)
    rcases h z with hz' | hexp | hlen
    · exact (hz hz').elim
    · right; left
      have h2 : z^2 ≤ y^2 := pow_le_pow_left' hzy 2
      have ht : 2*z ≤ 2*y := mul_le_mul_left hzy
      have ht2 : 2*z^2 ≤ 2*y^2 := mul_le_mul_left h2
      have hpoly : PRANegExponentialWitnessBound.negExponentialMajorant z ≤ PRANegExponentialWitnessBound.negExponentialMajorant y := by
        unfold PRANegExponentialWitnessBound.negExponentialMajorant
        exact add_le_add (add_le_add ht le_rfl) (add_le_add ht2 le_rfl)
      have hmy : PRANegExponentialWitnessBound.negExponentialMajorant y ≤ negBitMajorant y := le_trans le_self_add le_self_add
      have hw : PRANegExponentialWitnessBound.negExponentialMajorant z ≤ negBitMajorant y := le_trans hpoly hmy
      have hf : (∼expDef.val).Evalb ![z,x] := by simpa using hexp
      have hb := PRANegExpWitnessBound.neg_exp_bound z x hf
      have hs0 : Fin.snoc ![z,x] (PRANegExponentialWitnessBound.negExponentialMajorant z) = ![z,x,PRANegExponentialWitnessBound.negExponentialMajorant z] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hb' := eval_bnd_mono (∼expDef.val) ![z,x] (Empty.elim : Empty → V) hw (by rw [hs0]; exact hb)
      let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
      have hn := PRABndRewriting.natural (∼expDef.val) ω ![z,x,y] (negBitMajorant y)
      have hv : (fun j => (ω #j).val ![z,x,y] Empty.elim) = ![z,x] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hs : Fin.snoc ![z,x,y] (negBitMajorant y) = ![z,x,y,negBitMajorant y] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      rw [hv,hs] at hn
      have hh := hn.mpr hb'
      have heq : (ω ▹ (∼expDef.val)) = ∼(ω ▹ expDef.val) := by
        exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) expDef.val
      rw [heq] at hh
      exact hh
    · right; right
      let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
      have hf : (ω ▹ (∼lenbitDef.val)).Evalb ![z,x,y] := by simpa [ω, Semiformula.eval_substs] using hlen
      have hb := PRANegLenbitRewritingBound.neg_lenbit_rew_bound ω ![z,x,y] hf
      have hs0 : Fin.snoc ![z,x,y] (y+1) = ![z,x,y,y+1] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      have hb' := eval_bnd_mono (ω ▹ (∼lenbitDef.val)) ![z,x,y] (Empty.elim : Empty → V) hyw hb
      have hs : Fin.snoc ![z,x,y] (negBitMajorant y) = ![z,x,y,negBitMajorant y] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      rw [hs] at hb'
      have heq : (ω ▹ (∼lenbitDef.val)) = ∼(ω ▹ lenbitDef.val) := by
        exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) lenbitDef.val
      rw [heq] at hb'
      exact hb' 
def negBit : ArithmeticSemisentence 2 := ∼bitDef.val

def boundedNegBit : ArithmeticSemisentence 3 := bnd negBit

def negBitBoundBody : ArithmeticSemisentence 2 :=
  “x y. !negBit x y → !boundedNegBit x y (((2*y+1)+(2*y²+1))+y+1)”

theorem negBitBoundBody_model (e : Fin 2 → V) : negBitBoundBody.Eval e Empty.elim := by
  simp [negBitBoundBody, boundedNegBit, Semiformula.eval_substs]
  exact negBit_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negBitBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negBitBoundBody

theorem candidate_proves_negBit_bound : PRA ⊢ negBitBoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negBitBoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negBitBoundBody_model e
end DiophantineConsistency.PRANegBitFullWitnessBound
