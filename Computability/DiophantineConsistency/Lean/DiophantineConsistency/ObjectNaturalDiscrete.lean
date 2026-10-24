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

theorem zero_or_add_one (x : N H) : x=0 ∨ ∃ y : N H, x=y+1 := by
  rcases nat_zero_or_succ H x.val x.property with hz | ⟨y,hy,he⟩
  · exact Or.inl (Subtype.ext hz)
  · right
    refine ⟨⟨y,hy⟩,Subtype.ext ?_⟩
    change x.val=addValue H y (natV H 1)
    change x.val=addValue H y (vsucc H (vempty H))
    rw [addValue_succ_right H hy (vempty_in_omega H),addValue_zero_right H hy]
    exact he

theorem add_one_ne_zero (x : N H) : x+1≠0 := by
  intro h
  exact one_ne_zero ((ObjectResidualSquares.add_eq_zero_iff H x 1).mp h).2

theorem lt_iff_exists_add_one (x y : N H) : x<y ↔ ∃ s : N H, y=x+s+1 := by
  constructor
  · intro h
    obtain ⟨d,hd⟩ := (ObjectNaturalOrder.Natural.le_iff_exists_add H x y).mp h.le
    have hd0 : d≠0 := by
      intro hz
      have he : x=y := by simpa only [hz,add_zero] using hd
      exact h.ne he
    rcases zero_or_add_one H d with hzero | ⟨s,hs⟩
    · exact False.elim (hd0 hzero)
    · exact ⟨s,by rw [← hd,hs,add_assoc]⟩
  · rintro ⟨s,rfl⟩
    apply lt_of_le_of_ne
    · exact (ObjectNaturalOrder.Natural.le_iff_exists_add H x (x+s+1)).mpr
        ⟨s+1,by rw [add_assoc]⟩
    · intro he
      have hz : s+1=0 := add_left_cancel (a := x) (by
        simpa only [add_zero,add_assoc] using he.symm)
      exact add_one_ne_zero H s hz

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
