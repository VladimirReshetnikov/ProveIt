import IPRADerivations.Topology.MetricNets

/-!
# Helly's theorem on the line, with the median as witness

Packet: `geometry/helly-ipra`, `helly.tex`, Theorem `thm:main` for `d = 1`, `n = 3` (so `h = d + 1 = 2`): one
point is supplied for every pair of the three sets, `a` for the pair omitting the first set, `b` for the pair
omitting the second, `c` for the pair omitting the third. Every set contains two of the three points, hence
(being convex) the interval between them. The witness is the median, a term:

* `le_meet`: the greatest-lower-bound property of `meet`;
* `med a b c = join (meet a b) (meet (join a b) c)`;
* `helly_line`: for each of the three pairs `{u, v}` of supplied points,
  `meet u v ≤ med a b c ≤ join u v`, so the median lies in each of the three sets.
-/

namespace LeanProofs.IPRA.Geometry.HellyLine

open_ipra
open LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel (meet meet_left meet_right meet_le_left
  meet_le_right)
open LeanProofs.IPRA.Topology.MetricNets (join le_join_left le_join_right join_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A common lower bound is below the minimum. -/
theorem le_meet {a b c : PTm n} (ha : Γ ⊢[PRAAx] le c a) (hb : Γ ⊢[PRAAx] le c b) :
    Γ ⊢[PRAAx] le c (meet a b) := by
  refine .orE (le_total a b) ?_ ?_
  · have h : (le a b :: Γ) ⊢[PRAAx] le a b := Prf.hyp0
    have ha' := ha.wk (ψ := le a b)
    ipra_le sl ha' with natEq (meet_left h)
  · have h : (le b a :: Γ) ⊢[PRAAx] le b a := Prf.hyp0
    have hb' := hb.wk (ψ := le b a)
    ipra_le sl hb' with natEq (meet_right h)

/-- The median of three terms. -/
def med (a b c : PTm n) : PTm n := join (meet a b) (meet (join a b) c)

/-- Helly on the line for three sets: the median of the three supplied points lies between every two of
them. -/
theorem helly_line (a b c : PTm n) :
    ((Γ ⊢[PRAAx] le (meet a b) (med a b c)) ∧ (Γ ⊢[PRAAx] le (med a b c) (join a b))) ∧
      ((Γ ⊢[PRAAx] le (meet a c) (med a b c)) ∧ (Γ ⊢[PRAAx] le (med a b c) (join a c))) ∧
      ((Γ ⊢[PRAAx] le (meet b c) (med a b c)) ∧ (Γ ⊢[PRAAx] le (med a b c) (join b c))) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact le_join_left (meet a b) (meet (join a b) c)
  · exact join_le (le_trans (meet_le_left a b) (le_join_left a b)) (meet_le_left (join a b) c)
  · exact le_trans (le_meet (le_trans (meet_le_left a c) (le_join_left a b)) (meet_le_right a c))
      (le_join_right (meet a b) (meet (join a b) c))
  · exact join_le (le_trans (meet_le_left a b) (le_join_left a c))
      (le_trans (meet_le_right (join a b) c) (le_join_right a c))
  · exact le_trans (le_meet (le_trans (meet_le_left b c) (le_join_right a b)) (meet_le_right b c))
      (le_join_right (meet a b) (meet (join a b) c))
  · exact join_le (le_trans (meet_le_right a b) (le_join_left b c))
      (le_trans (meet_le_right (join a b) c) (le_join_right b c))

end LeanProofs.IPRA.Geometry.HellyLine
