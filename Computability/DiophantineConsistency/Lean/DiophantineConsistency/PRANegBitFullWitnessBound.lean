import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegExpWitnessBound
import DiophantineConsistency.PRANegLenbitWitnessBound
import DiophantineConsistency.PRARewritingWitnessBound
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
      let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
      have hf : (ω ▹ (∼expDef.val)).Evalb ![z,x,y] := by
        simpa [ω, Semiformula.eval_substs] using hexp
      have hw' : PRANegExponentialWitnessBound.negExponentialMajorant
          ((ω #0).val ![z,x,y] Empty.elim) ≤ negBitMajorant y := by
        simpa [ω] using hw
      have hh := PRARewritingWitnessBound.binary_rew_bound_with (∼expDef.val)
        (fun z _ => PRANegExponentialWitnessBound.negExponentialMajorant z)
        PRANegExpWitnessBound.neg_exp_bound ω ![z,x,y] (negBitMajorant y) hw' hf
      rw [show (ω ▹ (∼expDef.val)) = ∼(ω ▹ expDef.val) from
        LogicalConnective.HomClass.map_neg (Semiformula.rew ω) expDef.val] at hh
      simpa using hh
    · right; right
      let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#2]
      have hf : (ω ▹ (∼lenbitDef.val)).Evalb ![z,x,y] := by simpa [ω, Semiformula.eval_substs] using hlen
      have hw : ((ω #1).val ![z,x,y] Empty.elim)+1 ≤ negBitMajorant y := by
        simpa [ω] using hyw
      have hb := PRARewritingWitnessBound.binary_rew_bound_with (∼lenbitDef.val)
        (fun _ y => y+1) PRANegLenbitWitnessBound.neg_lenbit_bound
        ω ![z,x,y] (negBitMajorant y) hw hf
      rw [show (ω ▹ (∼lenbitDef.val)) = ∼(ω ▹ lenbitDef.val) from
        LogicalConnective.HomClass.map_neg (Semiformula.rew ω) lenbitDef.val] at hb
      simpa using hb
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
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negBitBoundBody_model e
end DiophantineConsistency.PRANegBitFullWitnessBound
