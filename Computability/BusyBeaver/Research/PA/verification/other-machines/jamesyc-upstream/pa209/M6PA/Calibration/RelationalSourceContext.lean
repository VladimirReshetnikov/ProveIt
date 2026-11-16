module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceND
@[expose] public section
/-! Actual finite open-parameter context discharge. Every premise is an
explicit native proof at the same free environment and allocator. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder NativeCalculus NativeCalculus.ActualBasis

def contextNegativeProof (xs : List (Proposition language))
    (f : Nat → Nat) (lo z : Nat)
    (suppliers : ∀ p,p ∈ xs → Proof (code p f lo z))
    (q : Proposition language) (hq : q ∈ xs.map Semiformula.neg) :
    Proof (wn (code q f lo z)) := by
  cases xs with
  | nil => exact False.elim (List.not_mem_nil hq)
  | cons a xs =>
    by_cases e : q = Semiformula.neg a
    · subst q
      let hp := suppliers a (by simp)
      let hn := negationProof a Fin.elim0 f lo z
      exact .mp (.mp hp (doubleNegationIntroduction _)) (contrapose hn.1)
    · exact contextNegativeProof xs f lo z
        (fun p hp => suppliers p (List.mem_cons_of_mem _ hp)) q
        ((List.mem_cons.mp hq).resolve_left e)

def compileContext (xs : List (Proposition language)) (σ : Proposition language)
    (d : ND.Proof xs σ) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i,f i < lo) (hz : lo + lkBudget d ≤ z)
    (suppliers : ∀ p,p ∈ xs → Proof (code p f lo z)) : Proof (code σ f lo z) := by
  let r : Refutes (ND.negatives xs + ⦃σ⦄) f lo z :=
    fun {C} => compileLK d f lo z hlo hf hz
  exact (r.positive (fun p hp =>
    .closed (contextNegativeProof xs f lo z suppliers p hp))).empty

#print axioms compileContext
end M6.PA.RelationalSource

