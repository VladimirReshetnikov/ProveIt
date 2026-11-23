import IPRADerivations.Combinatorics.Turan

/-!
# The admissible residues of a Steiner triple system

Packet: `combinatorics/Combinatorics-iPRA`, `structure.tex`, result 44 ("Necessary Steiner triple parameters"):
"If `v ≥ 3` points carry a family of triples through every pair exactly once, then `v ≡ 1` or `3 (mod 6)`". The
proof: "The equations `2r = v − 1` and `3b = vr` force `v` odd and `3 ∣ v(v − 1)`; checking residues modulo `6`
leaves `1, 3`." The two equations are `Combinatorics/DesignCounts.steiner_replication` (`2r = p` on `p + 1`
points) and `steiner_blocks` (`6b = (p + 1) p`), with `r` and `b` integer terms. As iPRA derivations, the
excluded residues are contradictory:

* `mul_ne_add`: `d x = d m + c` with `0 < c < d` is contradictory for an integer term `x` (a multiple of `d` is
  not congruent to `c`), by the strict totality `Combinatorics/Turan.zlt_or_zle`;
* `steiner_even`: `2r = 2m + 1` is contradictory: `v − 1` is even, so `v` is odd;
* `steiner_five`: `6b = (6m + 5)(6m + 4)` is contradictory: `v ≢ 5 (mod 6)`.

Hence `v ≡ 1` or `3 (mod 6)`. Not derived: the statements on parallel classes.
-/

namespace LeanProofs.IPRA.Combinatorics.SteinerResidues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Turan (zlt_or_zle)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `d x = d m + c` with `0 < c < d` is contradictory. -/
theorem mul_ne_add (d m c : ℕ) (hc : 1 ≤ c) (hcd : c + 1 ≤ d) {x : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.natLit d * x) (ZT.natLit (d * m + c))) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ := by
  obtain ⟨c1, hc1⟩ : ∃ c1, c = c1 + 1 := ⟨c - 1, by omega⟩
  obtain ⟨d1, hd1⟩ : ∃ d1, d = c + 1 + d1 := ⟨d - c - 1, by omega⟩
  refine .orE (zlt_or_zle x (ZT.natLit m)) ?_ ?_
  · have hlt : (zle (ZT.natLit m + ZT.natLit 1) x :: Γ) ⊢[PRAAx] zle (ZT.natLit m + ZT.natLit 1) x :=
      Prf.hyp0
    have e := ZT.toZ_eq (h.wk (ψ := zle (ZT.natLit m + ZT.natLit 1) x))
    simp only [ZT.toZ_mul, ZT.toZ_natLit] at e
    push_cast at e
    have hd1c := congrArg (Nat.cast : ℕ → Groth (Q (zle (ZT.natLit m + ZT.natLit 1) x :: Γ))) hd1
    push_cast at hd1c
    refine false_of_comb ((d : Groth (Q _)) * zsl hlt + (d1 : Groth (Q _))) ?_
      (nn_add (nn_mul (nn_natCast d) (nn_zsl _)) (nn_natCast d1)) _
    zsimp
    linear_combination e - hd1c
  · have hle : (zle x (ZT.natLit m) :: Γ) ⊢[PRAAx] zle x (ZT.natLit m) := Prf.hyp0
    have e := ZT.toZ_eq (h.wk (ψ := zle x (ZT.natLit m)))
    simp only [ZT.toZ_mul, ZT.toZ_natLit] at e
    push_cast at e
    have hc1c := congrArg (Nat.cast : ℕ → Groth (Q (zle x (ZT.natLit m) :: Γ))) hc1
    push_cast at hc1c
    refine false_of_comb ((d : Groth (Q _)) * zsl hle + (c1 : Groth (Q _))) ?_
      (nn_add (nn_mul (nn_natCast d) (nn_zsl _)) (nn_natCast c1)) _
    zsimp
    linear_combination (-1 : Groth (Q _)) * e - hc1c

/-- `2r = 2m + 1` is contradictory: the number of points of a Steiner triple system is odd. -/
theorem steiner_even (m : ℕ) {r : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * r) (ZT.natLit (2 * m + 1))) (φ : Fm PTm n) : Γ ⊢[PRAAx] φ :=
  mul_ne_add 2 m 1 (by norm_num) (by norm_num) h φ

/-- `6b = (6m + 5)(6m + 4)` is contradictory: the number of points is not `5` modulo `6`. -/
theorem steiner_five (m : ℕ) {B : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 6 * B) (ZT.natLit ((6 * m + 5) * (6 * m + 4)))) (φ : Fm PTm n) :
    Γ ⊢[PRAAx] φ := by
  have e : (6 * m + 5) * (6 * m + 4) = 6 * (6 * m * m + 9 * m + 3) + 2 := by ring
  rw [e] at h
  exact mul_ne_add 6 _ 2 (by norm_num) (by norm_num) h φ

end LeanProofs.IPRA.Combinatorics.SteinerResidues
