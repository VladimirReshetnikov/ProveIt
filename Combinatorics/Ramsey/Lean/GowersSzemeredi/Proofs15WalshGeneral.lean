import GowersSzemeredi.Sections14_15

/-! **Lemma 15.1 and Corollary 15.2 for arbitrary coefficients** (Notes L.16).

The printed Lemma 15.1 and Corollary 15.2 assume a ternary coefficient
function `η : {0,1}^k → {−1, 0, 1}`. The proofs never use it: the moment at
`A = [k]`, evaluated at two points differing in one coordinate, already
forces `η(e with e_j = 0) = −η(e with e_j = 1)`. So constancy of all
polynomial moments makes **every** integer coefficient function a modular
multiple of parity:
* `signedWalsh_multiple_of_invariant` (sign cube);
* `booleanWalsh_multiple_of_invariant` (Boolean cube).

The printed statements are the ternary cases: `lemma_15_1_holds`
(`Proofs15Walsh`) and `corollary_15_2_holds` (`Proofs15Walsh2`) apply these
theorems and drop the unused hypothesis.

This is what Lemma 15.4 needs for coefficient patterns in `[−m, m]` rather
than `{−1, 0, 1}`, as required by the Fejér selection of L.16. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Pointwise ZMod
open Finset
namespace LeanProofs.GowersSzemeredi

/-- **Lemma 15.1 without the ternary hypothesis.** Constancy of all
polynomial moments on the sign cube forces any integer coefficient function
to be a scalar multiple of parity modulo an odd prime. -/
theorem signedWalsh_multiple_of_invariant {N k : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (h : Point N k)
    (eta : (Fin k → Bool) → Int) (hh : ∀ i, h i ≠ 0)
    (hinvariant : ∀ (A : Finset (Fin k)) (y z : Point N k),
      signedWalshMoment eta h y A = signedWalshMoment eta h z A) :
    IsModularMultiple eta (fun e => ∏ i, walshSign (N := N) (e i)) := by
  letI : Fact (Nat.Prime N) := ⟨hprime⟩
  have htwo : (2 : ZMod N) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime 2 N).mpr (Nat.coprime_two_left.mpr hodd)).ne_zero
  -- Flipping coordinate `j` negates `eta`: at `y t` (coordinate `j` equal to `t`, every other
  -- coordinate cancelling the vertices that differ from `e` there) the full moment only sees
  -- the two vertices `e[j ↦ b]`; it is affine in `t` with slope
  -- `(eta e[j ↦ false] + eta e[j ↦ true]) * K`, which constancy forces to vanish.
  have hflip (e : Fin k → Bool) (j : Fin k) :
      (eta (Function.update e j false) : ZMod N) =
        -(eta (Function.update e j true) : ZMod N) := by
    let y : ZMod N → Point N k := fun t i => if i = j then t else walshSign (N := N) (e i) * h i
    let K : ZMod N := ∏ i ∈ univ.erase j, 2 * walshSign (N := N) (e i) * h i
    have hK : K ≠ 0 := prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (mul_ne_zero htwo (by cases e i <;> simp [walshSign])) (hh i)
    have hprod (t : ZMod N) (b : Bool) :
        ∏ i, (y t i + walshSign (N := N) (Function.update e j b i) * h i) =
          (t + walshSign (N := N) b * h j) * K := by
      rw [← mul_prod_erase _ _ (mem_univ j)]
      refine congrArg₂ _ (by simp [y]) (prod_congr rfl fun i hi => ?_)
      simp [y, ne_of_mem_erase hi]
      ring
    have hmom (t : ZMod N) : signedWalshMoment eta h (y t) univ =
        (eta (Function.update e j false) * (t - h j) +
          eta (Function.update e j true) * (t + h j)) * K := by
      rw [signedWalshMoment, Fintype.sum_eq_add (Function.update e j false)
        (Function.update e j true) (fun hft => by simpa using congrFun hft j), hprod, hprod]
      · simp [walshSign]
        ring
      rintro u ⟨huf, hut⟩
      obtain ⟨i, hij, hui⟩ : ∃ i, i ≠ j ∧ u i ≠ e i := by
        by_contra! hno
        cases hb : u j
        · exact huf (Function.eq_update_iff.mpr ⟨hb, hno⟩)
        · exact hut (Function.eq_update_iff.mpr ⟨hb, hno⟩)
      refine mul_eq_zero_of_right _ (prod_eq_zero (mem_univ i) ?_)
      simp only [y, if_neg hij]
      revert hui
      cases e i <;> cases u i <;> simp [walshSign]
    have := hinvariant univ (y 0) (y 1)
    rw [hmom, hmom] at this
    apply mul_right_cancel₀ hK
    linear_combination -this
  -- hence `eta` at the vertex that is `false` exactly on `s` is `(-1)^|s|` times its value at
  -- the all-`true` vertex, and so is the Walsh product
  let uOf : Finset (Fin k) → Fin k → Bool := fun s i => i ∉ s
  have key (s : Finset (Fin k)) :
      (eta (uOf s) : ZMod N) = (-1) ^ s.card * (eta (uOf ∅) : ZMod N) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert j s hjs ih =>
        have h1 : uOf (insert j s) = Function.update (uOf s) j false := by
          funext i
          by_cases hij : i = j <;> simp [uOf, hij]
        have h2 : Function.update (uOf s) j true = uOf s := by simp [uOf, hjs]
        rw [h1, hflip, h2, ih, card_insert_of_notMem hjs, pow_succ]
        ring
  refine ⟨(eta (uOf ∅) : ZMod N), fun e => ?_⟩
  obtain ⟨s, rfl⟩ : ∃ s, uOf s = e :=
    ⟨univ.filter (e · = false), funext fun i => by simp [uOf]⟩
  rw [key, mul_comm]
  congr 1
  simp [uOf, walshSign]

theorem parityCharacter_eq_prod {N k : Nat}
    (e : Fin k → Bool) :
    parityCharacter (N := N) e =
      ∏ i : Fin k,
        if e i then (-1 : ZMod N) else 1 := by
  simp only [parityCharacter, boolWeight, countWhere]
  rw [← Finset.prod_const, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : e i = true <;> simp [h]

theorem walshProduct_eq_parity {N k : Nat}
    (e : Fin k → Bool) :
    (∏ i : Fin k, walshSign (N := N) (e i)) =
      (-1 : ZMod N) ^ k * parityCharacter (N := N) e := by
  rw [parityCharacter_eq_prod]
  have hconst :
      (-1 : ZMod N) ^ k =
        ∏ _i : Fin k, (-1 : ZMod N) := by simp
  rw [hconst, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases e i <;> simp [walshSign]

/-- **Corollary 15.2 without the ternary hypothesis.** Constancy of all
polynomial moments on the Boolean cube forces any integer coefficient
function to be a scalar multiple of parity modulo an odd prime. -/
theorem booleanWalsh_multiple_of_invariant {N k : Nat} [NeZero N]
    (hprime : N.Prime) (hodd : Odd N) (h : Point N k)
    (eta : (Fin k → Bool) → Int) (hh : ∀ i, h i ≠ 0)
    (hinvariant : ∀ (A : Finset (Fin k)) (y z : Point N k),
      booleanWalshMoment eta h y A = booleanWalshMoment eta h z A) :
    IsModularMultiple eta (parityCharacter (N := N)) := by
  letI : Fact (Nat.Prime N) := ⟨hprime⟩
  have htwo : (2 : ZMod N) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime 2 N).mpr (Nat.coprime_two_left.mpr hodd)).ne_zero
  -- the sign cube of half the side lengths centred at `y` is the Boolean cube at `y - h / 2`
  have hmom (A : Finset (Fin k)) (y : Point N k) :
      signedWalshMoment eta (h · / 2) y A =
        booleanWalshMoment eta h (fun i => y i - h i / 2) A := by
    refine sum_congr rfl fun e _ => congrArg (_ * ·) (prod_congr rfl fun i _ => ?_)
    cases e i <;> simp [walshSign] <;> field_simp <;> ring
  obtain ⟨c, hc⟩ := signedWalsh_multiple_of_invariant hprime hodd (h · / 2) eta
    (fun i => div_ne_zero (hh i) htwo) fun A y z => by rw [hmom, hmom]; exact hinvariant A _ _
  exact ⟨c * (-1) ^ k, fun e => by rw [hc e, mul_assoc, ← walshProduct_eq_parity]⟩

end LeanProofs.GowersSzemeredi
