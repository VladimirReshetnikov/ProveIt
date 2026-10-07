import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {I R : Type*} [DecidableEq I] [CommSemiring R]

noncomputable def squarefreePermanent :
    (n : ℕ) → Finset I → (Fin n → I → R) → R
  | 0, S, _ => if S = ∅ then 1 else 0
  | n + 1, S, u => ∑ j ∈ S, u 0 j * squarefreePermanent n (S.erase j) (Fin.tail u)

noncomputable def squarefreeEmbeddingHeadEquiv (n : ℕ) (S : Finset I) :
    (Fin (n + 1) ↪ S) ≃ Σ j : S, Fin n ↪ (S.erase j.val) where
  toFun f := ⟨f 0, ⟨fun i => ⟨(f i.succ).val,
    Finset.mem_erase.mpr ⟨fun h => Fin.succ_ne_zero i (f.injective (Subtype.ext h)),
      (f i.succ).property⟩⟩,
    fun i j h => Fin.succ_injective _ (f.injective (Subtype.ext (congrArg (fun z : S.erase (f 0).val => z.val) h)))⟩⟩
  invFun p := ⟨Fin.cons p.1 (fun i => ⟨(p.2 i).val, (Finset.mem_erase.mp (p.2 i).property).2⟩), by
    intro i j h
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        exact False.elim ((Finset.mem_erase.mp (p.2 j).property).1 (congrArg Subtype.val h).symm)
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        exact False.elim ((Finset.mem_erase.mp (p.2 i).property).1 (congrArg Subtype.val h))
      | succ j => exact congrArg Fin.succ (p.2.injective (Subtype.ext (congrArg (fun z : S => z.val) h)))⟩
  left_inv f := by
    ext i
    cases i using Fin.cases <;> rfl
  right_inv p := by
    cases p with
    | mk j f =>
      congr 1

theorem squarefreePermanent_eq_embedding_sum (n : ℕ) (S : Finset I)
    (hS : S.card = n) (u : Fin n → I → R) :
    squarefreePermanent n S u = ∑ f : Fin n ↪ S, ∏ i, u i (f i).val := by
  induction n generalizing S with
  | zero =>
    have : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simp [squarefreePermanent]
  | succ n ih =>
    rw [squarefreePermanent]
    have hterm (j : S) :
        squarefreePermanent n (S.erase j.val) (Fin.tail u) =
          ∑ f : Fin n ↪ S.erase j.val, ∏ i, Fin.tail u i (f i).val :=
      ih _ (by rw [Finset.card_erase_of_mem j.property, hS]; omega) _
    calc
      _ = ∑ j : S, u 0 j.val * squarefreePermanent n (S.erase j.val) (Fin.tail u) := by
        exact (Finset.sum_coe_sort S (fun j => u 0 j * squarefreePermanent n (S.erase j) (Fin.tail u))).symm
      _ = ∑ j : S, ∑ f : Fin n ↪ S.erase j.val,
            u 0 j.val * ∏ i, Fin.tail u i (f i).val := by
        simp_rw [hterm, Finset.mul_sum]
      _ = ∑ p : Σ j : S, Fin n ↪ S.erase j.val,
            u 0 p.1.val * ∏ i, Fin.tail u i (p.2 i).val := by rw [Fintype.sum_sigma]
      _ = _ := by
        apply Fintype.sum_equiv (squarefreeEmbeddingHeadEquiv n S).symm
        intro p
        rw [Fin.prod_univ_succ]
        rfl

theorem squarefreePermanent_eq_matrix_permanent (n : ℕ) (S : Finset I)
    (e : Fin n ≃ S) (u : Fin n → I → R) :
    squarefreePermanent n S u = Matrix.permanent (fun i j => u i (e j).val) := by
  have hS : S.card = n := by
    simpa using (Fintype.card_congr e).symm
  rw [squarefreePermanent_eq_embedding_sum n S hS]
  rw [← Matrix.permanent_transpose (fun i j : Fin n => u i (e j).val)]
  let E : (Fin n ↪ S) ≃ Equiv.Perm (Fin n) :=
    ((Equiv.refl (Fin n)).embeddingCongr e.symm).trans (Equiv.embeddingEquivOfFinite (Fin n))
  unfold Matrix.permanent
  symm
  apply Fintype.sum_equiv E.symm
  intro σ
  apply Finset.prod_congr rfl
  intro i _
  rfl

theorem squarefreePermanent_image_eq_permanent (n : ℕ) (v : Fin n → I)
    (hv : Function.Injective v) (u : Fin n → I → R) :
    squarefreePermanent n (Finset.univ.image v) u =
      Matrix.permanent (fun i j => u i (v j)) := by
  let e : Fin n ≃ (Finset.univ.image v : Finset I) :=
    Equiv.ofBijective (fun i => ⟨v i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩) (by
      constructor
      · intro i j h
        exact hv (congrArg Subtype.val h)
      · intro j
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.property
        exact ⟨i, Subtype.ext hi⟩)
  exact squarefreePermanent_eq_matrix_permanent n _ e u

end Erdos3

end

end OAI
