/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
import OAI.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem APFree.integer_nonnegative_pullback {A : Set ℕ} {k : ℕ}
    (hA : APFree A k) (hk : 0 < k) :
    IntegerVectorAPFree {x : Unit → ℤ | 0 ≤ x () ∧ (x ()).toNat ∈ A} k := by
  classical
  intro a d hd
  by_contra h
  have hall (i : ℕ) (hi : i < k) :
      0 ≤ a () + (i : ℤ) * d () ∧ (a () + (i : ℤ) * d ()).toNat ∈ A := by
    have hp : a + (i : ℤ) • d ∈ {x : Unit → ℤ | 0 ≤ x () ∧ (x ()).toNat ∈ A} := by
      by_contra hn
      exact h ⟨⟨i, hi⟩, hn⟩
    simpa only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hp
  have hd0 : d () ≠ 0 := by
    intro he
    apply hd
    funext j
    cases j
    exact he
  apply hA
  rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
  · let b := a () + ((k - 1 : ℕ) : ℤ) * d ()
    have hb : 0 ≤ b := (hall (k - 1) (by omega)).1
    refine ⟨b.toNat, (-d ()).toNat, by omega, ?_⟩
    intro i hi
    have hj : k - 1 - i < k := by omega
    have he : (b.toNat + i * (-d ()).toNat : ℕ) =
        (a () + ((k - 1 - i : ℕ) : ℤ) * d ()).toNat := by
      have hindex : ((k - 1 - i : ℕ) : ℤ) + (i : ℤ) = ((k - 1 : ℕ) : ℤ) := by omega
      have hecast : ((b.toNat + i * (-d ()).toNat : ℕ) : ℤ) =
          a () + ((k - 1 - i : ℕ) : ℤ) * d () := by
        push_cast
        rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg (by omega : 0 ≤ -d ())]
        dsimp only [b]
        nlinarith [hindex]
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hecast
    rw [he]
    exact (hall _ hj).2
  · have ha : 0 ≤ a () := by simpa using (hall 0 hk).1
    refine ⟨(a ()).toNat, (d ()).toNat, by omega, ?_⟩
    intro i hi
    have he : (a ()).toNat + i * (d ()).toNat = (a () + (i : ℤ) * d ()).toNat := by
      have hecast : (((a ()).toNat + i * (d ()).toNat : ℕ) : ℤ) =
          a () + (i : ℤ) * d () := by
        push_cast
        rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hdpos.le]
      simpa only [Int.toNat_natCast] using congrArg Int.toNat hecast
    rw [he]
    exact (hall i hi).2

theorem integerBox_unit_expect (N : ℕ) (f : (Unit → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox (fun _ : Unit => N), f x) =
      𝔼 n : Fin N, f (fun _ => (n.val : ℤ)) := by
  classical
  symm
  apply Finset.expect_bij (fun (n : Fin N) _ (_ : Unit) => (n.val : ℤ))
  · intro n _
    exact (mem_integerBox _ _).mpr (fun _ => ⟨Int.natCast_nonneg _, by exact_mod_cast n.isLt⟩)
  · intro n _
    rfl
  · intro n _ m _ he
    apply Fin.ext
    exact_mod_cast congrFun he ()
  · intro x hx
    have hx' := (mem_integerBox _ _).mp hx ()
    refine ⟨⟨(x ()).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    funext j
    cases j
    exact Int.toNat_of_nonneg hx'.1

namespace APFreeInterval

noncomputable def integerIndicator {k : ℕ} (S : APFreeInterval k) (x : Unit → ℤ) : ℝ :=
  intervalIndicator S.points (x ()).toNat

@[simp] theorem integerIndicator_nat {k : ℕ} (S : APFreeInterval k) (n : ℕ) :
    S.integerIndicator (fun _ => (n : ℤ)) = intervalIndicator S.points n := by
  simp [integerIndicator]

theorem integerIndicator_mem_Icc {k : ℕ} (S : APFreeInterval k) (x : Unit → ℤ) :
    S.integerIndicator x ∈ Set.Icc (0 : ℝ) 1 :=
  intervalIndicator_mem_Icc _ _

theorem integerIndicator_mean {k : ℕ} (S : APFreeInterval k) :
    (𝔼 x ∈ integerBox (fun _ : Unit => S.length), S.integerIndicator x) = S.density := by
  rw [integerBox_unit_expect]
  simp only [integerIndicator_nat]
  exact mean_intervalIndicator S.subset

theorem integerIndicator_apFree {k : ℕ} (S : APFreeInterval k) (hk : 0 < k) :
    IntegerVectorAPFree {x | x ∈ integerBox (fun _ : Unit => S.length) ∧
      S.integerIndicator x ≠ 0} k := by
  intro a d hd
  obtain ⟨i, hi⟩ := S.free.integer_nonnegative_pullback hk a d hd
  refine ⟨i, ?_⟩
  rintro ⟨hbox, hnonzero⟩
  apply hi
  refine ⟨((mem_integerBox _ _).mp hbox ()).1, ?_⟩
  by_contra hmem
  exact hnonzero (ite_eq_right hmem)

end APFreeInterval

end Erdos3

end

end OAI
