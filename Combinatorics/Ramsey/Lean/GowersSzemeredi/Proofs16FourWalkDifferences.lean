import GowersSzemeredi.Proofs16GraphFourWalks

/-! Edge differences determine a four-walk up to translation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def fourWalkSteps {N : Nat} (u v : ZMod N) (t : ZMod N × ZMod N × ZMod N) : Fin 4 → ZMod N :=
  ![u-t.1,t.1-t.2.1,t.2.1-t.2.2,t.2.2-v]

/-- Equal edge differences mean that the two walks are translates. -/
theorem fourWalkSteps_equal_iff {N : Nat} (u v u' v' : ZMod N)
    (t t' : ZMod N × ZMod N × ZMod N) :
    fourWalkSteps u v t = fourWalkSteps u' v' t' ↔
      u-u' = t.1-t'.1 ∧ u-u' = t.2.1-t'.2.1 ∧
      u-u' = t.2.2-t'.2.2 ∧ u-u' = v-v' := by
  constructor
  · intro h
    have h0 : u-t.1 = u'-t'.1 := congrFun h 0
    have h1 : t.1-t.2.1 = t'.1-t'.2.1 := congrFun h 1
    have h2 : t.2.1-t.2.2 = t'.2.1-t'.2.2 := congrFun h 2
    have h3 : t.2.2-v = t'.2.2-v' := congrFun h 3
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination h0
    · linear_combination h0+h1
    · linear_combination h0+h1+h2
    · linear_combination h0+h1+h2+h3
  · rintro ⟨h0,h1,h2,h3⟩
    funext i; fin_cases i
    · change u-t.1 = u'-t'.1
      linear_combination h0
    · change t.1-t.2.1 = t'.1-t'.2.1
      linear_combination h1-h0
    · change t.2.1-t.2.2 = t'.2.1-t'.2.2
      linear_combination h2-h1
    · change t.2.2-v = t'.2.2-v'
      linear_combination h3-h2

/-- Once the starting point is fixed, the edge-difference sequence
uniquely determines every remaining vertex. -/
theorem fourWalkSteps_start_injective {N : Nat} (u : ZMod N) :
    Function.Injective (fun p : ZMod N × (ZMod N × ZMod N × ZMod N) => fourWalkSteps u p.1 p.2) := by
  intro p q h
  obtain ⟨h0,h1,h2,h3⟩ := (fourWalkSteps_equal_iff u p.1 u q.1 p.2 q.2).mp h
  have he : p.1 = q.1 := by linear_combination -h3
  have ha : p.2.1 = q.2.1 := by linear_combination -h0
  have hb : p.2.2.1 = q.2.2.1 := by linear_combination -h1
  have hc : p.2.2.2 = q.2.2.2 := by linear_combination -h2
  exact Prod.ext he (Prod.ext ha (Prod.ext hb hc))

end LeanProofs.GowersSzemeredi
