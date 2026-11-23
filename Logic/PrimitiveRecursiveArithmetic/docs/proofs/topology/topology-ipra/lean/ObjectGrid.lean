import IPRADerivations.Core.IntCertificates

/-! Fixed rectangle, symbolic entries. The output at each size is a derivation
in ordinary iPRA. This source is intended for the pinned ProveIt workspace.
The uniform numerical theorem (width and height as object terms) is a
separate target. See the formalization section of topology.pdf. -/

namespace LeanProofs.IPRA.Topology.GridWinding
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm
variable {n : ℕ} {Γ : List (Fm PTm n)}

def pSum (f : ℕ → ZT n) : ℕ → ZT n
  | 0 => ZT.natLit 0
  | w + 1 => pSum f w + f w

theorem strip (b t v : ℕ → ZT n) (w : ℕ)
    (cell : ∀ i, i < w → Γ ⊢[PRAAx] ZT.eq (b i + v (i + 1)) (v i + t i)) :
    Γ ⊢[PRAAx] ZT.eq (pSum b w + v w) (v 0 + pSum t w) := by
  induction w with
  | zero =>
    apply ZT.derive
    simp only [pSum, ZT.toZ_add, ZT.toZ_natLit]
    ring
  | succ w ih =>
    have prev := ih (fun i hi => cell i (Nat.lt_trans hi (Nat.lt_succ_self w)))
    have a := ZT.toZ_eq prev
    have b' := ZT.toZ_eq (cell w (Nat.lt_succ_self w))
    simp only [ZT.toZ_add] at a b'
    apply ZT.derive
    simp only [pSum, ZT.toZ_add]
    linear_combination a + b'

theorem periodicRows (h v : ℕ → ℕ → ZT n) (w height : ℕ)
    (cell : ∀ j, j < height → ∀ i, i < w →
      Γ ⊢[PRAAx] ZT.eq (h j i + v j (i + 1)) (v j i + h (j + 1) i))
    (seam : ∀ j, j < height → Γ ⊢[PRAAx] ZT.eq (v j w) (v j 0)) :
    Γ ⊢[PRAAx] ZT.eq (pSum (h 0) w) (pSum (h height) w) := by
  induction height with
  | zero =>
    apply ZT.derive
    rfl
  | succ j ih =>
    have prev := ih
      (fun k hk => cell k (Nat.lt_trans hk (Nat.lt_succ_self j)))
      (fun k hk => seam k (Nat.lt_trans hk (Nat.lt_succ_self j)))
    have lastRow := strip (h j) (h (j+1)) (v j) w (cell j (Nat.lt_succ_self j))
    have a := ZT.toZ_eq prev
    have b' := ZT.toZ_eq lastRow
    have c := ZT.toZ_eq (seam j (Nat.lt_succ_self j))
    simp only [ZT.toZ_add] at b'
    apply ZT.derive
    linear_combination a + b' - c

end LeanProofs.IPRA.Topology.GridWinding
