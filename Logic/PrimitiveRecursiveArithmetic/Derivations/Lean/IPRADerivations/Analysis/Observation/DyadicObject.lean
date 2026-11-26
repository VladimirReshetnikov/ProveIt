import IPRADerivations.Core.BoundedSums

/-! Imported from the packet `analysis/constructive_computable_analysis_ipra_2026-11-20`, `lean/DyadicObject.lean`: the namespace is placed under `LeanProofs.IPRA.Analysis` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! Object-language slope refinement for arbitrary signed dyadic observations.
All values have been scaled to a common positive integer denominator. -/
namespace LeanProofs.IPRA.Analysis.Observation.DyadicObject
open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

def delta (x y : ZT n) : ZT n := ⟨x.pos + y.neg, x.neg + y.pos⟩

def twice (x : ZT n) : ZT n := ⟨x.pos + x.pos, x.neg + x.neg⟩

/-- The object formula asserting that two signed numbers differ by at most e. -/
def close (e : PTm n) (u v : ZT n) : Fm PTm n :=
  le (u.pos + v.neg) (v.pos + u.neg + e) ⋏
  le (v.pos + u.neg) (u.pos + v.neg + e)

/-- The adjacent-child bound is transported to both child/parent
discrepancies after multiplying by the width of the parent cell. -/
theorem child_from_adjacent (left mid right : ZT n) (e : PTm n)
    (h : Γ ⊢[PRAAx] close e (delta right mid) (delta mid left)) :
    Γ ⊢[PRAAx] close e (twice (delta mid left)) (delta right left) ⋏
      close e (twice (delta right mid)) (delta right left) := by
  simp only [close, delta, twice] at h ⊢
  have hi := h.andE₁
  have lo := h.andE₂
  refine .andI (.andI ?_ ?_) (.andI ?_ ?_)
  · exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (left.pos + left.neg) lo)
  · exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (left.pos + left.neg) hi)
  · exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (right.pos + right.neg) hi)
  · exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (right.pos + right.neg) lo)

def body : Fm PTm 7 :=
  let l := ZT.var2 0 1
  let m := ZT.var2 2 3
  let r := ZT.var2 4 5
  let e := (var 6 : PTm 7)
  close e (delta r m) (delta m l) ⟶
    (close e (twice (delta m l)) (delta r l) ⋏
     close e (twice (delta r m)) (delta r l))

/-- Universal closure over the three signed pairs and the error radius. -/
def sentence : Fm PTm 0 := .all (.all (.all (.all (.all (.all (.all body))))))

theorem child_from_adjacent_closed : [] ⊢[PRAAx] sentence := by
  unfold sentence
  repeat' apply Prf.allI
  exact .impI (child_from_adjacent _ _ _ _ Prf.hyp0)

end LeanProofs.IPRA.Analysis.Observation.DyadicObject
