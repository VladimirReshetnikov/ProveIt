import FabiusFunction.ThueMorseBinomialLog
import Mathlib.Computability.Partrec

/-!
# The Thue–Morse sequence is primitive recursive

The Thue–Morse sequence is defined by a *digit* condition — the parity of
the number of ones in the binary expansion of `n` — and not by an
ordinary primitive recursion, since the natural recurrence

`t(2n) = t(n)`,  `t(2n+1) = ¬t(n)`

calls itself at `n / 2` rather than at `n - 1`.  This module supplies the
missing scheme and deduces that every incarnation of the sequence used in
this corpus — Boolean, `{0,1}`-valued, and `{±1}`-valued — is primitive
recursive, hence computable.

## The reusable scheme

`primrec_of_descent` is the general statement: a recursion whose recursive
call is at `d n` for *any* primitive recursive `d` with `d n < n` is
primitive recursive.  This is course-of-values recursion in the form one
actually meets in digit combinatorics, and it is proved from Mathlib's
`Primrec.nat_strong_rec` by reading the value `f (d n)` off the list of
already-computed values `[f 0, …, f (n-1)]`.  The `n = 0` case is handled
without a case split: on the empty list the lookup returns `none`, and
`Option.getD` supplies the base value.

`primrec_of_halving` specializes it to `d n = n / 2`, the shape of every
base-two digit recursion.

## The Thue–Morse results

* `binaryWeight_div_two` — the halving recurrence `w n = w (n / 2) + n % 2`.
* `primrec_binaryWeight` — the binary digit sum is primitive recursive.
* `primrec_thueMorseBool`, `primrec_thueMorseBit`, `primrec_thueMorseSign`
  — the sequence itself, in its three incarnations.
* `nat_primrec_binaryWeight`, `nat_primrec_thueMorseBit` — the same claim
  in the textbook form `Nat.Primrec`, for functions `ℕ → ℕ`.
* `computable_thueMorseBool`, `computable_thueMorseBit`,
  `computable_thueMorseSign` — the computability corollaries.

The `{±1}`-valued sign is obtained *without* any integer arithmetic:
every function out of `Bool` is primitive recursive (`Primrec.dom_bool`),
so the sign is the composite of the Boolean word with `fun b => cond b (-1) 1`.
-/

namespace Fabius

set_option autoImplicit false

/-! ## A reusable primitive-recursion scheme -/

/-- **Recursion along a primitive recursive descent is primitive recursive.**

If `d` is primitive recursive and strictly decreasing in the sense that
`d n < n` for `n > 0`, and `f` satisfies `f 0 = z` together with
`f n = g n (f (d n))` for `n > 0` with `g` primitive recursive, then `f`
is primitive recursive.

This is the practical form of course-of-values recursion: the recursive
call may jump anywhere below `n`, not merely to `n - 1`.  Note that no
hypothesis is placed on `d 0`. -/
theorem primrec_of_descent {σ : Type*} [Primcodable σ] {f : ℕ → σ} {z : σ}
    {d : ℕ → ℕ} {g : ℕ → σ → σ} (hd : Primrec d) (hg : Primrec₂ g)
    (hdlt : ∀ n, 0 < n → d n < n) (h0 : f 0 = z)
    (hrec : ∀ n, 0 < n → f n = g n (f (d n))) : Primrec f := by
  -- The step function reads `f (d n)` off the list of computed values.
  have hG : Primrec₂ (fun (_ : Unit) (L : List σ) =>
      (some ((L[d L.length]?.map (g L.length)).getD z) : Option σ)) := by
    have hlen : Primrec (fun p : Unit × List σ => p.2.length) :=
      Primrec.list_length.comp Primrec.snd
    have hget : Primrec (fun p : Unit × List σ => p.2[d p.2.length]?) :=
      Primrec.list_getElem?.comp Primrec.snd (hd.comp hlen)
    have hstep : Primrec₂ (fun (p : Unit × List σ) (s : σ) => g p.2.length s) :=
      hg.comp (hlen.comp Primrec.fst) Primrec.snd
    have hmap : Primrec (fun p : Unit × List σ =>
        (p.2[d p.2.length]?).map (g p.2.length)) :=
      Primrec.option_map hget hstep
    exact Primrec.option_some.comp
      (Primrec.option_getD.comp hmap (Primrec.const z))
  have key : Primrec₂ (fun (_ : Unit) (n : ℕ) => f n) := by
    refine Primrec.nat_strong_rec _ hG ?_
    intro _ n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0]
    · have hlt : d n < n := hdlt n hn
      simp only [List.length_map, List.length_range]
      rw [List.getElem?_map, List.getElem?_range hlt]
      simp [hrec n hn]
  exact key.comp (Primrec.const ()) Primrec.id

/-- **Halving recursion is primitive recursive**: the base-two case of
`primrec_of_descent`, which is the shape of every binary digit recursion.
If `f 0 = z` and `f n = g n (f (n / 2))` for `n > 0` with `g` primitive
recursive, then `f` is primitive recursive. -/
theorem primrec_of_halving {σ : Type*} [Primcodable σ] {f : ℕ → σ} {z : σ}
    {g : ℕ → σ → σ} (hg : Primrec₂ g) (h0 : f 0 = z)
    (hrec : ∀ n, 0 < n → f n = g n (f (n / 2))) : Primrec f :=
  primrec_of_descent
    (Primrec.nat_div.comp Primrec.id (Primrec.const 2)) hg
    (fun _ hn => Nat.div_lt_self hn one_lt_two) h0 hrec

/-! ## The binary digit sum -/

/-- **The halving recurrence for the binary weight**: `w n = w (n / 2) + n % 2`.
Stripping the last binary digit removes exactly that digit from the sum.
The identity holds at `n = 0` as well, where both sides vanish. -/
theorem binaryWeight_div_two (n : ℕ) :
    binaryWeight n = binaryWeight (n / 2) + n % 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [binaryWeight]
  · rw [binaryWeight, binaryWeight, Nat.digits_def' one_lt_two hn,
      List.sum_cons]
    omega

/-- **The binary digit sum is primitive recursive.** -/
theorem primrec_binaryWeight : Primrec binaryWeight := by
  refine primrec_of_halving (z := 0) (g := fun n s => s + n % 2) ?_ ?_ ?_
  · exact Primrec.nat_add.comp Primrec.snd
      (Primrec.nat_mod.comp Primrec.fst (Primrec.const 2))
  · simp [binaryWeight]
  · exact fun n _ => binaryWeight_div_two n

/-- The binary digit sum is primitive recursive in the textbook sense
`Nat.Primrec`, i.e. it lies in the least class of functions `ℕ → ℕ`
containing the successor and projections and closed under composition and
primitive recursion. -/
theorem nat_primrec_binaryWeight : Nat.Primrec binaryWeight :=
  Primrec.nat_iff.mp primrec_binaryWeight

/-! ## The Thue–Morse sequence -/

/-- The Thue–Morse sequence as a Boolean word: `true` at `n` exactly when
the binary expansion of `n` has an odd number of ones. -/
def thueMorseBool (n : ℕ) : Bool := binaryWeight n % 2 == 1

/-- The Boolean word is `true` exactly at the odd-weight indices. -/
theorem thueMorseBool_eq_true_iff (n : ℕ) :
    thueMorseBool n = true ↔ Odd (binaryWeight n) := by
  rw [thueMorseBool, beq_iff_eq, ← Nat.odd_iff]

/-- The Boolean word is `true` exactly where the `{0,1}`-valued bit is `1`:
the two normalizations of the sequence agree. -/
theorem thueMorseBool_eq_true_iff_bit (n : ℕ) :
    thueMorseBool n = true ↔ thueMorseBit n = 1 := by
  rw [thueMorseBool, thueMorseBit, beq_iff_eq]

/-- **The doubling relation** `t(2n) = t(n)`: appending a zero digit does
not change the parity of the digit sum. -/
@[simp] theorem thueMorseBool_two_mul (n : ℕ) :
    thueMorseBool (2 * n) = thueMorseBool n := by
  simp [thueMorseBool, binaryWeight_two_mul]

/-- **The flip relation** `t(2n+1) = ¬t(n)`: appending a one digit flips
the parity of the digit sum. -/
@[simp] theorem thueMorseBool_two_mul_add_one (n : ℕ) :
    thueMorseBool (2 * n + 1) = !thueMorseBool n := by
  have h : binaryWeight n % 2 = 0 ∨ binaryWeight n % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one _
  rcases h with h | h <;>
    simp [thueMorseBool, binaryWeight_two_mul_add_one, Nat.add_mod, h]

/-- **The Thue–Morse word is primitive recursive.** -/
theorem primrec_thueMorseBool : Primrec thueMorseBool :=
  Primrec.beq.comp
    (Primrec.nat_mod.comp primrec_binaryWeight (Primrec.const 2))
    (Primrec.const 1)

/-- **The `{0,1}`-valued Thue–Morse sequence is primitive recursive.** -/
theorem primrec_thueMorseBit : Primrec thueMorseBit :=
  Primrec.nat_mod.comp primrec_binaryWeight (Primrec.const 2)

/-- The `{0,1}`-valued sequence is primitive recursive in the textbook
sense `Nat.Primrec`. -/
theorem nat_primrec_thueMorseBit : Nat.Primrec thueMorseBit :=
  Primrec.nat_iff.mp primrec_thueMorseBit

/-- The sign is read off the Boolean word. -/
theorem thueMorseSign_eq_cond (n : ℕ) :
    thueMorseSign n = cond (thueMorseBool n) (-1) 1 := by
  rcases Nat.even_or_odd (binaryWeight n) with h | h
  · rw [thueMorseSign, h.neg_one_pow, thueMorseBool, Nat.even_iff.mp h]
    rfl
  · rw [thueMorseSign, h.neg_one_pow, thueMorseBool, Nat.odd_iff.mp h]
    rfl

/-- **The `{±1}`-valued Thue–Morse sequence is primitive recursive.**

No integer arithmetic is needed: every function out of `Bool` is
primitive recursive, so the sign is the Boolean word followed by
`fun b => cond b (-1) 1`. -/
theorem primrec_thueMorseSign : Primrec thueMorseSign :=
  ((Primrec.dom_bool (fun b : Bool => cond b (-1 : ℤ) 1)).comp
    primrec_thueMorseBool).of_eq fun n => (thueMorseSign_eq_cond n).symm

/-! ## Computability -/

/-- The binary digit sum is computable. -/
theorem computable_binaryWeight : Computable binaryWeight :=
  primrec_binaryWeight.to_comp

/-- **The Thue–Morse word is computable.** -/
theorem computable_thueMorseBool : Computable thueMorseBool :=
  primrec_thueMorseBool.to_comp

/-- **The `{0,1}`-valued Thue–Morse sequence is computable.** -/
theorem computable_thueMorseBit : Computable thueMorseBit :=
  primrec_thueMorseBit.to_comp

/-- **The `{±1}`-valued Thue–Morse sequence is computable.** -/
theorem computable_thueMorseSign : Computable thueMorseSign :=
  primrec_thueMorseSign.to_comp

/-- Membership in the Thue–Morse set `{n | t n = true}` is a primitive
recursive predicate; unfolding the definition, this is exactly the
statement that the set is primitive recursively decidable. -/
theorem primrecPred_thueMorseBool :
    PrimrecPred (fun n => thueMorseBool n = true) :=
  ⟨inferInstance, primrec_thueMorseBool.of_eq fun n => by simp⟩

/-- Membership in the Thue–Morse set is decidable by a total algorithm:
the deciding function is computable. -/
theorem computable_decide_thueMorseBool :
    Computable (fun n => decide (thueMorseBool n = true)) :=
  (primrec_thueMorseBool.of_eq fun n => by simp).to_comp

end Fabius
