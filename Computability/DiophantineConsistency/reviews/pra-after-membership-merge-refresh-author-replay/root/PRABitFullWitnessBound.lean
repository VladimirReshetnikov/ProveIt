import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAExpWitnessBound
import DiophantineConsistency.PRABitWitnessBound
/-! Bound the actual positive Foundation bitDef graph, discharging its
    bounded exponential premise. The fixpoint and refutation bounds remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRABitFullWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem majorant_mono {z y : V} (h : z ≤ y) :
    PRAExponentialWitnessBound.exponentialMajorant z ≤ PRAExponentialWitnessBound.exponentialMajorant y := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have h4 : z^4 ≤ y^4 := pow_le_pow_left' h 4
  have h2 : z^2 ≤ y^2 := pow_le_pow_left' h 2
  have ht2 : 2*z^2 ≤ 2*y^2 := mul_le_mul_left h2
  have ht1 : 2*z ≤ 2*y := mul_le_mul_left h
  unfold PRAExponentialWitnessBound.exponentialMajorant
  exact add_le_add (add_le_add (add_le_add (add_le_add h4 le_rfl) (add_le_add h2 le_rfl))
      (add_le_add ht2 le_rfl)) (add_le_add (add_le_add (add_le_add h4 h4) ht1) le_rfl)
attribute [local irreducible] expDef

def bitMajorant (y : V) := PRAExponentialWitnessBound.exponentialMajorant y + y + 1

theorem bit_bound (x y : V) : bitDef.val.Evalb ![x,y] →
    (bnd bitDef.val).Evalb ![x,y,bitMajorant y] := by
  intro h
  simp [bitDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs] at h
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rcases h with ⟨z,hz,hexp,hlen⟩
  have hzy : z ≤ y := lt_succ_iff_le.mp hz
  have hy : y ≤ PRAExponentialWitnessBound.exponentialMajorant y+y := le_add_self
  have hyw : y+1 ≤ bitMajorant y := by simpa [bitMajorant,add_comm] using add_le_add_right hy 1
  have hmy : PRAExponentialWitnessBound.exponentialMajorant y ≤ bitMajorant y := le_trans le_self_add le_self_add
  have hmz : PRAExponentialWitnessBound.exponentialMajorant z ≤ bitMajorant y := le_trans (majorant_mono hzy) hmy
  have hb := PRAExpWitnessBound.exp_bound z x hexp
  have hs0 : Fin.snoc ![z,x] (PRAExponentialWitnessBound.exponentialMajorant z) = ![z,x,PRAExponentialWitnessBound.exponentialMajorant z] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hb' := eval_bnd_mono expDef.val ![z,x] (Empty.elim : Empty → V) hmz (by rw [hs0]; exact hb)
  let ω : Rew ℒₒᵣ Empty 2 Empty 3 := Rew.subst ![#0,#1]
  have hn := PRABndRewriting.natural expDef.val ω ![z,x,y] (bitMajorant y)
  have hv : (fun j => (ω #j).val ![z,x,y] Empty.elim) = ![z,x] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs : Fin.snoc ![z,x,y] (bitMajorant y) = ![z,x,y,bitMajorant y] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hs' : Fin.snoc ![z,x] (bitMajorant y) = ![z,x,bitMajorant y] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  rw [hv,hs,hs'] at hn
  rw [hs'] at hb'
  have hbe : (bnd PRABitWitnessBound.expInsideBit).Evalb ![z,x,y,bitMajorant y] := hn.mpr hb'
  have hbl : PRABitWitnessBound.lenbitInsideBit.Evalb ![z,x,y] := by
    simpa [PRABitWitnessBound.lenbitInsideBit, Semiformula.eval_substs] using hlen
  exact PRABitWitnessBound.bit_bnd_of_witness x y (bitMajorant y) z hyw hzy hbe hbl
def boundedBit : ArithmeticSemisentence 3 := bnd bitDef.val

def bitBoundBody : ArithmeticSemisentence 2 :=
  “x y. !bitDef x y → !boundedBit x y (((y⁴+1)+(y²+1)+(2*y²+1)+(y⁴+y⁴+2*y+1))+y+1)”

theorem bitBoundBody_model (e : Fin 2 → V) : bitBoundBody.Eval e Empty.elim := by
  simp [bitBoundBody, boundedBit, Semiformula.eval_substs]
  exact bit_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def bitBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding bitBoundBody

theorem candidate_proves_bit_bound : PRA ⊢ bitBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact bitBoundBody_model e
end DiophantineConsistency.PRABitFullWitnessBound
