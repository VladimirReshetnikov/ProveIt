import IPRADerivations.Geometry.RadonPartition

/-!
# Making approximate coordinates simplex-valued

Packet: `topology/approximate_brouwer_ipra`, `brouwer.tex`, "Making approximate coordinates simplex-valued":
for a tuple `b` put `τ(b) = max_{∅ ≠ S} (∑_{i ∈ S} b_i − 1)/|S|` and `Π_i(b) = max{0, b_i − τ(b)}`. "Every
subset sum of `b_i − τ(b)` is at most `1`, and one is `1`. The largest subset sum is the sum of the positive
entries, hence `∑_i Π_i(b) = 1`."

The shifted coordinates `c_i = b_i − τ` are integer terms (cleared of denominators, `one` the unit), subsets
are Boolean masks, and the positive part is the term `pp` of `Geometry/RadonPartition`:

* `ssum bs cs`: the subset sum of the mask `bs`; `psum cs`: the sum of the positive parts;
* `pos_sum_le`: "The largest subset sum is the sum of the positive entries": if `t + ∑_S c_i ≤ B` for every
  subset `S`, then `t + ∑_i c_i^+ ≤ B` (by an object-level case split on the sign of each entry);
* `sub_le_pos`: every subset sum is at most the sum of the positive parts;
* `projection_mass`: if every subset sum is at most `one` and the subset `bs₀` attains it, then
  `∑_i c_i^+ = one`, that is `∑_i Π_i(b) = 1`.
-/

namespace LeanProofs.IPRA.Topology.SimplexProjection

open_ipra
open LeanProofs.IPRA.Geometry.RadonPartition (pp np toZ_parts parts_disjoint pp_nonneg np_nonneg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The sum of the entries selected by a Boolean mask. -/
def ssum : List Bool → List (ZT n) → ZT n
  | b :: bs, c :: cs => (if b then c else ZT.natLit 0) + ssum bs cs
  | _, _ => ZT.natLit 0

/-- The sum of the positive parts. -/
def psum : List (ZT n) → ZT n
  | [] => ZT.natLit 0
  | c :: cs => pp c + psum cs

/-- The largest subset sum is the sum of the positive entries. -/
theorem pos_sum_le : {Γ : List (Fm PTm n)} → (cs : List (ZT n)) → (t B : ZT n) →
    (∀ bs : List Bool, Γ ⊢[PRAAx] zle (t + ssum bs cs) B) → (Γ ⊢[PRAAx] zle (t + psum cs) B)
  | _, [], _, _, h => h []
  | Γ, c :: cs, t, B, h => by
    show Γ ⊢[PRAAx] zle (t + (pp c + psum cs)) B
    refine .orE (parts_disjoint c) ?_ ?_
    · have e0 : (ZT.eq (pp c) (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq (pp c) (ZT.natLit 0) := Prf.hyp0
      have e := ZT.toZ_eq e0
      simp only [ZT.toZ_natLit, Nat.cast_zero] at e
      have ih := pos_sum_le (Γ := ZT.eq (pp c) (ZT.natLit 0) :: Γ) cs t B fun bs => by
        have h'' : (ZT.eq (pp c) (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle (t + (ZT.natLit 0 + ssum bs cs)) B :=
          (h (false :: bs)).wk
        ipra_zle zsl h''
      ipra_zle (zsl ih) with -e
    · have e0 : (ZT.eq (np c) (ZT.natLit 0) :: Γ) ⊢[PRAAx] ZT.eq (np c) (ZT.natLit 0) := Prf.hyp0
      have e := ZT.toZ_eq e0
      simp only [ZT.toZ_natLit, Nat.cast_zero] at e
      have ep := toZ_parts (Γ := ZT.eq (np c) (ZT.natLit 0) :: Γ) c
      have ih := pos_sum_le (Γ := ZT.eq (np c) (ZT.natLit 0) :: Γ) cs (t + c) B fun bs => by
        have h'' : (ZT.eq (np c) (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle (t + (c + ssum bs cs)) B :=
          (h (true :: bs)).wk
        ipra_zle zsl h''
      ipra_zle (zsl ih) with -ep - e

/-- Every subset sum is at most the sum of the positive parts. -/
theorem sub_le_pos : (bs : List Bool) → (cs : List (ZT n)) → (Γ ⊢[PRAAx] zle (ssum bs cs) (psum cs))
  | [], [] => by
    show Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.natLit 0)
    ipra_zle 0
  | [], c :: cs => by
    have h' : Γ ⊢[PRAAx] zle (ZT.natLit 0) (psum cs) := sub_le_pos [] cs
    have hp := pp_nonneg (Γ := Γ) c
    show Γ ⊢[PRAAx] zle (ZT.natLit 0) (pp c + psum cs)
    ipra_zle zsl h' + zsl hp
  | _ :: _, [] => by
    show Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.natLit 0)
    ipra_zle 0
  | b :: bs, c :: cs => by
    have ih : Γ ⊢[PRAAx] zle (ssum bs cs) (psum cs) := sub_le_pos bs cs
    have hp := pp_nonneg (Γ := Γ) c
    have hn := np_nonneg (Γ := Γ) c
    have ep := toZ_parts (Γ := Γ) c
    cases b
    · show Γ ⊢[PRAAx] zle (ZT.natLit 0 + ssum bs cs) (pp c + psum cs)
      ipra_zle zsl ih + zsl hp
    · show Γ ⊢[PRAAx] zle (c + ssum bs cs) (pp c + psum cs)
      ipra_zle (zsl ih + zsl hn) with ep

/-- `∑_i Π_i(b) = 1`: every subset sum of the shifted coordinates is at most `one`, and one of them is
`one`. -/
theorem projection_mass (cs : List (ZT n)) (one : ZT n)
    (hall : ∀ bs : List Bool, Γ ⊢[PRAAx] zle (ssum bs cs) one) (bs₀ : List Bool)
    (hmax : Γ ⊢[PRAAx] ZT.eq (ssum bs₀ cs) one) : Γ ⊢[PRAAx] ZT.eq (psum cs) one := by
  have h₁ : Γ ⊢[PRAAx] zle (ZT.natLit 0 + psum cs) one := pos_sum_le cs (ZT.natLit 0) one fun bs => by
    have h := hall bs
    ipra_zle zsl h
  have h₂ := sub_le_pos (Γ := Γ) bs₀ cs
  have u : Γ ⊢[PRAAx] zle (psum cs) one := by
    ipra_zle zsl h₁
  have l : Γ ⊢[PRAAx] zle one (psum cs) := by
    refine zle_of_comb (zsl h₂) ?_ (nn_zsl _)
    rw [zsl_def, ZT.toZ_eq hmax]
  exact le_antisymm u l

end LeanProofs.IPRA.Topology.SimplexProjection
