import OAI.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def fullCubeSignal {G : Type*} [AddCommGroup G] {d : ℕ}
    (f : G → ℂ) (x : Fin (d + 3) → G) : ℂ :=
  cubeProduct f (List.ofFn (fun j => x ((1 : Fin (d + 3)).succAbove j))) (x 1)

theorem booleanWeight_true (d : ℕ) : booleanWeight (fun _ : Fin d => true) = d := by
  simp [booleanWeight]

theorem cubeShift_true {G : Type*} [AddCommGroup G] {d : ℕ} (k : Fin d → G) :
    cubeShift k (fun _ => true) = ∑ i, k i := by simp [cubeShift]

theorem exists_false_of_ne_true {d : ℕ} {ω : Fin d → Bool}
    (h : ω ≠ fun _ => true) : ∃ j, ω j = false := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  refine ⟨j, ?_⟩
  cases he : ω j <;> simp_all

theorem cubeShift_congr_selected {G : Type*} [AddCommGroup G] {d : ℕ}
    (k l : Fin d → G) (ω : Fin d → Bool) (h : ∀ i, ω i = true → k i = l i) :
    cubeShift k ω = cubeShift l ω := by
  unfold cubeShift
  apply Finset.sum_congr rfl
  intro i _
  cases hi : ω i with
  | false => simp only [Bool.false_eq_true, ite_false]
  | true => simp only [ite_true]; exact h i hi

theorem fullCube_input_independent {G : Type*} [AddCommGroup G] {d : ℕ}
    (ω : Fin (d + 2) → Bool) (j : Fin (d + 2)) (hj : ω j = false)
    (x y : Fin (d + 3) → G)
    (hxy : ∀ k, k ≠ (1 : Fin (d + 3)).succAbove j → x k = y k) :
    x 1 + cubeShift (fun k => x ((1 : Fin (d + 3)).succAbove k)) ω =
      y 1 + cubeShift (fun k => y ((1 : Fin (d + 3)).succAbove k)) ω := by
  rw [hxy 1 (Fin.ne_succAbove 1 j)]
  congr 1
  apply cubeShift_congr_selected
  intro k hk
  apply hxy
  intro heq
  have hkj : k = j := Fin.succAbove_right_injective heq
  subst k
  simp only [hj, Bool.false_eq_true] at hk

theorem mixedCubeInput_independent {d : ℕ} (ω : Fin d → Bool) (j : Fin d) (hj : ω j = false)
    (x y : Fin (d + 2) → ℤ) (hxy : ∀ k, k ≠ j.succ.succ → x k = y k) :
    mixedCubeInput ω x = mixedCubeInput ω y := by
  have hzero : (0 : Fin (d + 2)) ≠ j.succ.succ := (Fin.succ_ne_zero j.succ).symm
  have hone : (1 : Fin (d + 2)) ≠ j.succ.succ := by
    intro heq
    have h : (0 : Fin (d + 1)) = j.succ := Fin.succ_inj.mp heq
    exact (Fin.succ_ne_zero j).symm h
  unfold mixedCubeInput
  rw [hxy 0 hzero, hxy 1 hone]
  congr 2
  apply cubeShift_congr_selected
  intro k hk
  apply hxy
  intro heq
  have hkj : k = j := Fin.succ_inj.mp (Fin.succ_inj.mp heq)
  subst k
  simp only [hj, Bool.false_eq_true] at hk

theorem mixedCubeInput_true {d : ℕ} (x : Fin (d + 2) → ℤ) :
    mixedCubeInput (fun _ => true) x = correlationInput (x 0) (∑ j : Fin (d + 1), x j.succ) := by
  unfold mixedCubeInput
  rw [cubeShift_true]
  exact congrArg (correlationInput (x 0)) (Fin.sum_univ_succ (fun j : Fin (d + 1) => x j.succ)).symm

theorem fullCubeSignal_profile {d N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    fullCubeSignal (fun z : ℤ => f (z : ZMod N)) (mixedDifferencePoint t n) =
      cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) := by
  have htuple : (fun j => ((mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j) : ℤ) : ZMod N)) =
      Fin.cons (t.1 0) (mixedDifferenceShifts t) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [mixedDifferencePoint]
    · simp [Fin.one_succAbove_succ, mixedDifferencePoint]
  have hbase : mixedDifferencePoint t n 1 = n := rfl
  have hlist : List.ofFn t.1 = t.1 0 :: List.ofFn (Fin.tail t.1) := by
    rw [List.ofFn_succ]
    rfl
  unfold fullCubeSignal
  have hmap := cubeProduct_comp_addHom (Int.castAddHom (ZMod N)) f
    (List.ofFn (fun j => mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j)))
    (mixedDifferencePoint t n 1)
  simp only [Int.coe_castAddHom] at hmap
  rw [hmap, List.map_ofFn]
  change cubeProduct f
    (List.ofFn (fun j => ((mixedDifferencePoint t n ((1 : Fin (d + 3)).succAbove j) : ℤ) : ZMod N)))
    ((mixedDifferencePoint t n 1 : ℤ) : ZMod N) = _
  rw [htuple, hbase, List.ofFn_cons, mixedDifferenceShifts, List.ofFn_cons, hlist]
  exact cubeProduct_swap_head f (t.1 0) t.2 _ _

end Erdos3

end

end OAI
