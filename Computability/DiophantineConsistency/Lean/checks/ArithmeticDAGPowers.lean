import DiophantineConsistency.ArithmeticDAGPowers
open DiophantineConsistency.ArithmeticDAG
#print axioms run_power
#print axioms evalAt_of_NodeRel
#print axioms value_eq_of_powerRewrite

namespace PowerRewriteRegression
-- Two distinct addition chains for X^7, followed by a non-power output X^7+1.
def old : List (Node 1 0) := [.input 0,.literal 1,.mul 0 0,.mul 2 2,.mul 0 2,.mul 3 4,.add 5 1]
def new : List (Node 1 0) := [.input 0,.literal 1,.mul 0 0,.mul 0 2,.mul 2 3,.mul 2 4,.add 5 1]
def ol (i : ℕ) : ℕ := ([1,0,2,4,3,7,0] : List ℕ).getD i 0
def nl (i : ℕ) : ℕ := ([1,0,2,3,5,7,0] : List ℕ).getD i 0
def im (i : ℕ) : ℕ := ([0,1,0,0,0,0,6] : List ℕ).getD i 0
example {R : Type*} [CommRing R] (p : Fin 0 → R) (x : Fin 1 → R) :
    value new 6 p x = value old 6 p x := by
  apply value_eq_of_powerRewrite p x old new (by decide) (by decide) ol nl im 0 0 6 6
  · rfl
  · rfl
  · rfl
  · intro i hi
    have h : ∀ i : Fin 7, i.val ≠ 0 → ol i.val ≠ 0 → PowerStep old ol i.val := by decide
    exact h ⟨i,hi⟩
  · intro i hi
    have h : ∀ i : Fin 7, PowerRewriteStep old new ol nl im 0 i.val := by decide
    exact h ⟨i,hi⟩
  · decide
  · rfl
  · rfl
end PowerRewriteRegression
