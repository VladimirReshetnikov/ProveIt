import DiophantineConsistency.ObjectResidualSquares
import BoundedZFCConsistency.InternalSat
import BoundedZFCConsistency.CodedDerivation

/-! # Discrete order and Boolean polynomial roots on the entire internal omega -/
noncomputable section
namespace DiophantineConsistency.ObjectNaturalDiscrete
open SetTheory
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring ObjectArithmetic
open ObjectMultiplication ObjectMultiplicationLaws
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

theorem lt_add_one_iff (a b : N H) : a < b + 1 ↔ a ≤ b := by
  change mem a.val (b + 1).val ↔ a ≤ b
  rw [ObjectOmegaSemiring.Natural.val_add_one H b, vsucc_spec H b.val a.val]
  have he : a.val = b.val ↔ a = b := ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
  exact (or_congr Iff.rfl he).trans le_iff_lt_or_eq.symm

theorem add_one_le_iff (a b : N H) : a + 1 ≤ b ↔ a < b := by
  rw [← not_lt, lt_add_one_iff H b a, not_le]

theorem zero_or_add_one (x : N H) : x=0 ∨ ∃ y : N H, x=y+1 := by
  rcases nat_zero_or_succ H x.val x.property with hz | ⟨y,hy,he⟩
  · exact Or.inl (Subtype.ext hz)
  · exact Or.inr ⟨⟨y,hy⟩,Subtype.ext
      (he.trans (ObjectOmegaSemiring.Natural.val_add_one H ⟨y,hy⟩).symm)⟩

theorem add_one_ne_zero (x : N H) : x+1≠0 := by
  intro h
  exact one_ne_zero ((ObjectResidualSquares.add_eq_zero_iff H x 1).mp h).2

theorem lt_iff_exists_add_one (x y : N H) : x<y ↔ ∃ s : N H, y=x+s+1 := by
  rw [← add_one_le_iff H x y,ObjectNaturalOrder.Natural.le_iff_exists_add H]
  apply exists_congr
  intro s
  simpa only [add_right_comm x 1 s] using
    (eq_comm : (x+s+1=y) ↔ (y=x+s+1))

/-- This uses zero/successor decomposition on all internal naturals; algebra
alone would not force an idempotent in an arbitrary semiring to be Boolean. -/
theorem mul_self_eq_self_iff (x : N H) : x*x=x ↔ x=0 ∨ x=1 := by
  constructor
  · intro hx
    rcases zero_or_add_one H x with hz | ⟨s,hs⟩
    · exact Or.inl hz
    · have hprod : x*s=0 := by
        apply add_right_cancel (b := x)
        calc
          x*s+x=x*(s+1) := by ring
          _ = x*x := by rw [← hs]
          _ = x := hx
          _ = 0+x := (zero_add x).symm
      rcases mul_eq_zero.mp hprod with hx0 | hs0
      · exact Or.inl hx0
      · exact Or.inr (by simpa only [hs0,zero_add] using hs)
  · rintro (rfl | rfl) <;> simp

theorem cast_lt_cast (n m : ℕ) : (n : N H)<(m : N H) ↔ n<m := by
  have hm : StrictMono (fun k : ℕ => (k : N H)) := fun a b h => natV_lt H a b h
  exact hm.lt_iff_lt

end DiophantineConsistency.ObjectNaturalDiscrete
