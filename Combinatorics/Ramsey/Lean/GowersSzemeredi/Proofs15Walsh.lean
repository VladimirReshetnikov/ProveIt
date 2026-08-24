import GowersSzemeredi.Sections14_15

/-!
# Proven companion for Gowers (2001), Lemma 15.1
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- **Lemma 15.1 (Walsh basis).** Constancy of all polynomial moments
forces the coefficient function to be a scalar multiple of parity. -/
theorem lemma_15_1_holds : lemma_15_1 := by
  unfold lemma_15_1
  intro N k _ hprime hodd h eta hh _heta hinvariant
  letI : Fact (Nat.Prime N) := ⟨hprime⟩
  have hNgt : 2 < N := by
    have hle := hprime.two_le
    have hne : N ≠ 2 := by
      intro hN
      subst N
      exact hodd.not_two_dvd_nat (dvd_refl 2)
    omega
  have htwo : (2 : ZMod N) ≠ 0 := by
    intro hz
    have hdvd : N ∣ 2 :=
      (CharP.cast_eq_zero_iff (ZMod N) N 2).mp hz
    exact (Nat.not_le_of_lt hNgt)
      (Nat.le_of_dvd (by omega) hdvd)

  have hflip : ∀ (e : Fin k → Bool) (j : Fin k),
      (eta (Function.update e j false) : ZMod N) =
        -(eta (Function.update e j true) : ZMod N) := by
    intro e j
    classical
    let ef := Function.update e j false
    let et := Function.update e j true
    have heft : ef ≠ et := by
      intro heq
      have hj := congrFun heq j
      simp [ef, et] at hj
    let y : ZMod N → Point N k := fun t i =>
      if i = j then t else walshSign (N := N) (e i) * h i
    let term : ZMod N → (Fin k → Bool) → ZMod N := fun t u =>
      (eta u : ZMod N) * ∏ i : Fin k,
        (y t i + walshSign (N := N) (u i) * h i)

    have houtside (u : Fin k → Bool) (huf : u ≠ ef) (hut : u ≠ et) :
        ∃ i : Fin k, i ≠ j ∧ u i ≠ e i := by
      by_contra hno
      push Not at hno
      by_cases huj : u j = false
      · apply huf
        funext i
        by_cases hij : i = j
        · subst i
          simp [ef, huj]
        · simp [ef, hij, hno i hij]
      · have hujt : u j = true := by
          cases huv : u j
          · exact False.elim (huj huv)
          · rfl
        apply hut
        funext i
        by_cases hij : i = j
        · subst i
          simp [et, hujt]
        · simp [et, hij, hno i hij]

    have hterm_zero (t : ZMod N) (u : Fin k → Bool)
        (huf : u ≠ ef) (hut : u ≠ et) : term t u = 0 := by
      obtain ⟨i, hij, hui⟩ := houtside u huf hut
      have hfactor :
          y t i + walshSign (N := N) (u i) * h i = 0 := by
        simp only [y, if_neg hij]
        cases he : e i <;> cases hu : u i <;>
          simp_all [walshSign]
      have hp : (∏ a : Fin k,
          (y t a + walshSign (N := N) (u a) * h a)) = 0 := by
        exact Finset.prod_eq_zero (s := Finset.univ)
          (Finset.mem_univ i) hfactor
      simp only [term, hp, mul_zero]

    have hreduce (t : ZMod N) :
        signedWalshMoment eta h (y t) Finset.univ =
          term t ef + term t et := by
      unfold signedWalshMoment
      change (∑ u : Fin k → Bool, term t u) =
        term t ef + term t et
      rw [← Finset.sum_pair heft]
      symm
      exact Finset.sum_subset (by simp) (fun u _ hu => by
        simp only [Finset.mem_insert, Finset.mem_singleton,
          not_or] at hu
        exact hterm_zero t u hu.1 hu.2)

    let K : ZMod N := ∏ i ∈ Finset.univ.erase j,
      (2 : ZMod N) * walshSign (N := N) (e i) * h i
    have hK : K ≠ 0 := by
      unfold K
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact mul_ne_zero
        (mul_ne_zero htwo
          (by cases e i <;> simp [walshSign]))
        (hh i)

    have hprod (t : ZMod N) (b : Bool) :
        (∏ i : Fin k,
          (y t i +
            walshSign (N := N) ((Function.update e j b) i) *
              h i)) =
          (t + walshSign (N := N) b * h j) * K := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i : Fin k => y t i +
          walshSign (N := N) ((Function.update e j b) i) *
            h i)
        (Finset.mem_univ j)]
      congr 1
      · simp [y]
      · unfold K
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        simp [y, hij]
        ring

    have hmom := hinvariant Finset.univ (y 0) (y 1)
    rw [hreduce 0, hreduce 1] at hmom
    simp only [term, ef, et, hprod] at hmom
    have hzero :
        ((eta ef : ZMod N) + (eta et : ZMod N)) * K = 0 := by
      linear_combination -hmom
    have heta_sum :
        (eta ef : ZMod N) + (eta et : ZMod N) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hK
    exact eq_neg_iff_add_eq_zero.mpr heta_sum

  classical
  let uOf : Finset (Fin k) → (Fin k → Bool) := fun s i =>
    if i ∈ s then false else true
  have hu_insert (s : Finset (Fin k)) (j : Fin k)
      (hjs : j ∉ s) :
      uOf (insert j s) =
        Function.update (uOf s) j false := by
    funext i
    by_cases hij : i = j
    · subst i
      simp [uOf]
    · simp [uOf, hij]
  have hu_true (s : Finset (Fin k)) (j : Fin k)
      (hjs : j ∉ s) :
      Function.update (uOf s) j true = uOf s := by
    rw [Function.update_eq_self_iff]
    simp [uOf, hjs]
  have heta_uOf (s : Finset (Fin k)) :
      (eta (uOf s) : ZMod N) =
        (-1 : ZMod N) ^ s.card *
          (eta (uOf ∅) : ZMod N) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert j s hjs ih =>
        rw [hu_insert s j hjs, hflip (uOf s) j,
          hu_true s j hjs, ih,
          Finset.card_insert_of_notMem hjs, pow_succ]
        ring

  refine ⟨(eta (uOf ∅) : ZMod N), ?_⟩
  intro e
  let s : Finset (Fin k) :=
    Finset.univ.filter fun i => e i = false
  have hue : uOf s = e := by
    funext i
    cases he : e i <;> simp [uOf, s, he]
  rw [← hue, heta_uOf]
  have hsign :
      (∏ i : Fin k, walshSign (N := N) (uOf s i)) =
        (-1 : ZMod N) ^ s.card := by
    calc
      (∏ i : Fin k, walshSign (N := N) (uOf s i)) =
          ∏ i : Fin k,
            if i ∈ s then (-1 : ZMod N) else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases his : i ∈ s <;>
          simp [uOf, his, walshSign]
      _ = ∏ i ∈ s, (-1 : ZMod N) := by
        rw [← Finset.prod_filter (s := Finset.univ)
          (fun i : Fin k => i ∈ s)
          (fun _ => (-1 : ZMod N))]
        congr
        ext i
        simp [s]
      _ = (-1 : ZMod N) ^ s.card := by simp
  change
    (-1 : ZMod N) ^ s.card *
        (eta (uOf ∅) : ZMod N) =
      (eta (uOf ∅) : ZMod N) *
        ∏ i : Fin k, walshSign (N := N) (uOf s i)
  rw [hsign]
  ring

end LeanProofs.GowersSzemeredi
