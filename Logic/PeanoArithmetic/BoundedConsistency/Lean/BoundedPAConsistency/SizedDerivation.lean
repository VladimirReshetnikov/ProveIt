import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
import Mathlib.Tactic.Ring

/-!
# Size-bounded internal derivations

Foundation's internal derivability `Derivable T s` is `∃ d, DerivationOf T d s`:
it forgets the derivation code. For explicit (elementary) witness bounds we
need the code back with a bound, so this module introduces

`DerivableLe T s b :↔ ∃ d ≤ b, DerivationOf T d s`

and bounded twins of Foundation's rule lemmas (`Derivable.em`, `and_m`, …).

All bounds have one shape. The ten rule constructors are explicit Cantor
tuples `⟪s, k, …⟫ + 1` with at most six entries, and one pairing of two
numbers below `2^e` stays below `2^(4e)` (`pair_succ_le_exp`, for `e ≥ 3`).
So **if every entry of a rule is at most `2^e` (`e ≥ 4`), the rule's code is
at most `2^(1024·e)`** (`*_le` below). Formulas occurring in a sequent cost
nothing extra: a set code bounds its members (`p ∈ s → p < s`), and
`seq_lt_exp` bounds a set code by a bound on its members.

In an induction over derivations, a fixed number `k` of rule applications per
node multiplies the exponent by `1024^k`, which a tower bound
`2^(2^(a·n))` absorbs (`exp_add`). This keeps every witness map built on these
lemmas elementary recursive.

Everything holds in every model of `𝗜𝚺₁`, at arbitrary internal codes.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.BoundedPAConsistency.SizedDerivation

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Exponential arithmetic for Cantor pairs -/

section Arith

theorem exp_two : Exp.exp (2 : V) = 4 := by
  rw [show (2 : V) = 1 + 1 by norm_num, exp_succ, exp_one]
  norm_num

theorem le_exp_of_le {x e e' : V} (h : x ≤ Exp.exp e) (he : e ≤ e') : x ≤ Exp.exp e' :=
  le_trans h (exp_monotone_le.mpr he)

theorem le_exp_self (x : V) : x ≤ Exp.exp x := le_of_lt (lt_exp x)

theorem le_exp_of_le_self {x e : V} (h : x ≤ e) : x ≤ Exp.exp e :=
  le_trans h (le_exp_self e)

/-- A sequent (set) code is below `2^B` when all its members are below `B`. -/
theorem seq_lt_exp {s B : V} (h : ∀ y ∈ s, y < B) : s < Exp.exp B := lt_exp_iff.mpr h

theorem le_four_mul {e : V} : e ≤ 4 * e :=
  le_mul_of_one_le_left (Arithmetic.zero_le e) (by norm_num)

/-- **One Cantor pairing below `2^e` stays below `2^(4e)`, with room for `+1`.** -/
theorem pair_succ_le_exp {a b e : V} (he : 3 ≤ e) (ha : a ≤ Exp.exp e) (hb : b ≤ Exp.exp e) :
    ⟪a, b⟫ + 1 ≤ Exp.exp (4 * e) := by
  have h1 : (1 : V) ≤ Exp.exp e := one_le_exp e
  have hs : a + b + 1 ≤ Exp.exp (e + 2) := by
    rw [exp_add, exp_two]
    calc a + b + 1 ≤ Exp.exp e + Exp.exp e + Exp.exp e :=
          _root_.add_le_add (_root_.add_le_add ha hb) h1
      _ ≤ Exp.exp e + Exp.exp e + Exp.exp e + Exp.exp e := le_self_add
      _ = Exp.exp e * 4 := by ring
  have hp : ⟪a, b⟫ ≤ Exp.exp (2 * (e + 2)) := by
    rw [exp_even]
    exact le_trans (pair_polybound a b) (pow_le_pow_left₀ (Arithmetic.zero_le _) hs 2)
  have h2 : 2 * (e + 2) + 1 ≤ 4 * e := by
    have : 2 * (e + 2) + 1 + 1 ≤ 4 * e := by
      calc 2 * (e + 2) + 1 + 1 = 2 * e + 6 := by ring
        _ ≤ 2 * e + 2 * e := _root_.add_le_add le_rfl
            (le_trans (by norm_num : (6 : V) ≤ 2 * 3) (mul_le_mul_of_nonneg_left he (Arithmetic.zero_le 2)))
        _ = 4 * e := by ring
    exact le_trans le_self_add this
  calc ⟪a, b⟫ + 1 ≤ Exp.exp (2 * (e + 2)) + Exp.exp (2 * (e + 2)) :=
        _root_.add_le_add hp (one_le_exp _)
    _ = Exp.exp (2 * (e + 2) + 1) := by rw [exp_succ]; ring
    _ ≤ Exp.exp (4 * e) := exp_monotone_le.mpr h2

theorem pair_le_exp {a b e : V} (he : 3 ≤ e) (ha : a ≤ Exp.exp e) (hb : b ≤ Exp.exp e) :
    ⟪a, b⟫ ≤ Exp.exp (4 * e) :=
  le_trans le_self_add (pair_succ_le_exp he ha hb)

theorem three_le_four_mul {e : V} (he : 3 ≤ e) : 3 ≤ 4 * e := le_trans he le_four_mul

/-- Rule tags `0, …, 9` are below `2^e` once `e ≥ 4`. -/
theorem tag_le {k e : V} (hk : k ≤ 9) (he : 4 ≤ e) : k ≤ Exp.exp e := by
  have h16 : Exp.exp (4 : V) = 16 := by
    rw [show (4 : V) = 2 * 2 by norm_num, exp_even, exp_two]
    norm_num
  calc k ≤ 9 := hk
    _ ≤ 16 := by norm_num
    _ = Exp.exp 4 := h16.symm
    _ ≤ Exp.exp e := exp_monotone_le.mpr he

/-- Lift a `2^e` bound to `2^(4e)`. -/
theorem lift {x e : V} (h : x ≤ Exp.exp e) : x ≤ Exp.exp (4 * e) := le_exp_of_le h le_four_mul

end Arith

/-! ## Bounds for the ten rule codes -/

section Codes

variable {e : V}

private theorem le3 (he : 4 ≤ e) : 3 ≤ e := le_trans (by norm_num) he

private theorem le4 (he : 4 ≤ e) : 4 ≤ 4 * e := le_trans he le_four_mul

theorem mul1024 (e : V) : 4 * (4 * (4 * (4 * (4 * e)))) = 1024 * e := by ring

theorem exp_mono_mul {x k k' e : V} (h : x ≤ Exp.exp (k * e)) (hk : k ≤ k') :
    x ≤ Exp.exp (k' * e) :=
  le_exp_of_le h (mul_le_mul_of_nonneg_right hk (Arithmetic.zero_le e))

/-- Three-entry tuple `⟪a, b, c⟫ + 1`. -/
theorem tuple3_le {a b c : V} (he : 4 ≤ e) (ha : a ≤ Exp.exp e) (hb : b ≤ Exp.exp e)
    (hc : c ≤ Exp.exp e) : ⟪a, b, c⟫ + 1 ≤ Exp.exp (1024 * e) := by
  have h1 := pair_le_exp (le3 he) hb hc
  have h2 := pair_succ_le_exp (three_le_four_mul (le3 he)) (lift ha) h1
  refine le_trans h2 (exp_monotone_le.mpr ?_)
  rw [← mul1024]
  exact le_trans le_four_mul (le_trans le_four_mul le_four_mul)

/-- Four-entry tuple. -/
theorem tuple4_le {a b c d : V} (he : 4 ≤ e) (ha : a ≤ Exp.exp e) (hb : b ≤ Exp.exp e)
    (hc : c ≤ Exp.exp e) (hd : d ≤ Exp.exp e) : ⟪a, b, c, d⟫ + 1 ≤ Exp.exp (1024 * e) := by
  have e1 := le3 he
  have e2 := three_le_four_mul e1
  have e3 := three_le_four_mul e2
  have h1 := pair_le_exp e1 hc hd
  have h2 := pair_le_exp e2 (lift hb) h1
  have h3 := pair_succ_le_exp e3 (lift (lift ha)) h2
  refine le_trans h3 (exp_monotone_le.mpr ?_)
  rw [← mul1024]
  exact le_trans le_four_mul le_four_mul

/-- Five-entry tuple. -/
theorem tuple5_le {a b c d f : V} (he : 4 ≤ e) (ha : a ≤ Exp.exp e) (hb : b ≤ Exp.exp e)
    (hc : c ≤ Exp.exp e) (hd : d ≤ Exp.exp e) (hf : f ≤ Exp.exp e) :
    ⟪a, b, c, d, f⟫ + 1 ≤ Exp.exp (1024 * e) := by
  have e1 := le3 he
  have e2 := three_le_four_mul e1
  have e3 := three_le_four_mul e2
  have e4 := three_le_four_mul e3
  have h1 := pair_le_exp e1 hd hf
  have h2 := pair_le_exp e2 (lift hc) h1
  have h3 := pair_le_exp e3 (lift (lift hb)) h2
  have h4 := pair_succ_le_exp e4 (lift (lift (lift ha))) h3
  refine le_trans h4 (exp_monotone_le.mpr ?_)
  rw [← mul1024]
  exact le_four_mul

/-- Six-entry tuple. -/
theorem tuple6_le {a b c d f g : V} (he : 4 ≤ e) (ha : a ≤ Exp.exp e) (hb : b ≤ Exp.exp e)
    (hc : c ≤ Exp.exp e) (hd : d ≤ Exp.exp e) (hf : f ≤ Exp.exp e) (hg : g ≤ Exp.exp e) :
    ⟪a, b, c, d, f, g⟫ + 1 ≤ Exp.exp (1024 * e) := by
  have e1 := le3 he
  have e2 := three_le_four_mul e1
  have e3 := three_le_four_mul e2
  have e4 := three_le_four_mul e3
  have e5 := three_le_four_mul e4
  have h1 := pair_le_exp e1 hf hg
  have h2 := pair_le_exp e2 (lift hd) h1
  have h3 := pair_le_exp e3 (lift (lift hc)) h2
  have h4 := pair_le_exp e4 (lift (lift (lift hb))) h3
  have h5 := pair_succ_le_exp e5 (lift (lift (lift (lift ha)))) h4
  rw [← mul1024]
  exact h5

theorem axL_le {s p : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hp : p ≤ Exp.exp e) :
    axL s p ≤ Exp.exp (1024 * e) :=
  tuple3_le he hs (tag_le (by norm_num) he) hp

theorem verumIntro_le {s : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) :
    verumIntro s ≤ Exp.exp (1024 * e) :=
  tuple3_le he hs (tag_le (by norm_num) he) (tag_le (by norm_num) he)

theorem andIntro_le {s p q dp dq : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hp : p ≤ Exp.exp e)
    (hq : q ≤ Exp.exp e) (hdp : dp ≤ Exp.exp e) (hdq : dq ≤ Exp.exp e) :
    andIntro s p q dp dq ≤ Exp.exp (1024 * e) :=
  tuple6_le he hs (tag_le (by norm_num) he) hp hq hdp hdq

theorem orIntro_le {s p q d : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hp : p ≤ Exp.exp e)
    (hq : q ≤ Exp.exp e) (hd : d ≤ Exp.exp e) :
    orIntro s p q d ≤ Exp.exp (1024 * e) :=
  tuple5_le he hs (tag_le (by norm_num) he) hp hq hd

theorem allIntro_le {s p d : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hp : p ≤ Exp.exp e)
    (hd : d ≤ Exp.exp e) : allIntro s p d ≤ Exp.exp (1024 * e) :=
  tuple4_le he hs (tag_le (by norm_num) he) hp hd

theorem exsIntro_le {s p t d : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hp : p ≤ Exp.exp e)
    (ht : t ≤ Exp.exp e) (hd : d ≤ Exp.exp e) : exsIntro s p t d ≤ Exp.exp (1024 * e) :=
  tuple5_le he hs (tag_le (by norm_num) he) hp ht hd

theorem wkRule_le {s d : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hd : d ≤ Exp.exp e) :
    wkRule s d ≤ Exp.exp (1024 * e) :=
  tuple3_le he hs (tag_le (by norm_num) he) hd

theorem shiftRule_le {s d : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hd : d ≤ Exp.exp e) :
    shiftRule s d ≤ Exp.exp (1024 * e) :=
  tuple3_le he hs (tag_le (by norm_num) he) hd

theorem cutRule_le {s p d₁ d₂ : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hp : p ≤ Exp.exp e)
    (hd₁ : d₁ ≤ Exp.exp e) (hd₂ : d₂ ≤ Exp.exp e) : cutRule s p d₁ d₂ ≤ Exp.exp (1024 * e) :=
  tuple5_le he hs (tag_le (by norm_num) he) hp hd₁ hd₂

theorem axm_le {s p : V} (he : 4 ≤ e) (hs : s ≤ Exp.exp e) (hp : p ≤ Exp.exp e) :
    axm s p ≤ Exp.exp (1024 * e) :=
  tuple3_le he hs (tag_le (by norm_num) he) hp

end Codes

/-! ## Size-bounded derivability -/

variable {L : Language} [L.Encodable] [L.LORDefinable]

/-- `s` has a `T`-derivation with code at most `b`. -/
def DerivableLe (T : Theory L) [T.Δ₁] (s b : V) : Prop := ∃ d ≤ b, DerivationOf T d s

namespace DerivableLe

variable {T : Theory L} [T.Δ₁] {e : V}

theorem toDerivable {s b : V} (h : DerivableLe T s b) : Derivable T s :=
  let ⟨d, _, hd⟩ := h
  ⟨d, hd⟩

theorem mono {s b b' : V} (h : DerivableLe T s b) (hb : b ≤ b') : DerivableLe T s b' :=
  let ⟨d, hdb, hd⟩ := h
  ⟨d, le_trans hdb hb, hd⟩

theorem isFormulaSet {s b : V} (h : DerivableLe T s b) : IsFormulaSet L s :=
  h.toDerivable.isFormulaSet

theorem ofSetEq {s s' b : V} (h : ∀ x, x ∈ s' ↔ x ∈ s) (hd : DerivableLe T s' b) :
    DerivableLe T s b := by
  have : s' = s := mem_ext h
  rcases this
  exact hd

theorem of_ss {U : Theory L} [U.Δ₁] (h : T.Δ₁Class (V := V) ⊆ U.Δ₁Class) {s b : V} :
    DerivableLe T s b → DerivableLe U s b := by
  rintro ⟨d, hdb, hd⟩
  exact ⟨d, hdb, hd.1, hd.2.of_ss h⟩

theorem mem_le {p s : V} (hs : s ≤ Exp.exp e) (h : p ∈ s) : p ≤ Exp.exp e :=
  le_of_lt (lt_of_lt_of_le (lt_of_mem h) hs)

theorem em {s : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (hs : IsFormulaSet L s) (p : V)
    (h : p ∈ s) (hn : neg L p ∈ s) : DerivableLe T s (Exp.exp (1024 * e)) :=
  ⟨axL s p, axL_le he hsb (mem_le hsb h), by simp, Derivation.axL hs h hn⟩

theorem verum {s : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (hs : IsFormulaSet L s)
    (h : ^⊤ ∈ s) : DerivableLe T s (Exp.exp (1024 * e)) :=
  ⟨verumIntro s, verumIntro_le he hsb, by simp, Derivation.verumIntro hs h⟩

theorem and_m {s p q : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (h : p ^⋏ q ∈ s)
    (hp : DerivableLe T (insert p s) (Exp.exp e)) (hq : DerivableLe T (insert q s) (Exp.exp e)) :
    DerivableLe T s (Exp.exp (1024 * e)) := by
  rcases hp with ⟨dp, hdpb, hdp⟩
  rcases hq with ⟨dq, hdqb, hdq⟩
  have hpq := mem_le hsb h
  refine ⟨andIntro s p q dp dq, andIntro_le he hsb ?_ ?_ hdpb hdqb, by simp,
    Derivation.andIntro h hdp hdq⟩
  · exact le_trans (le_of_lt (lt_K!_left p q)) hpq
  · exact le_trans (le_of_lt (lt_K!_right p q)) hpq

theorem or_m {s p q : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (h : p ^⋎ q ∈ s)
    (hpq : DerivableLe T (insert p (insert q s)) (Exp.exp e)) :
    DerivableLe T s (Exp.exp (1024 * e)) := by
  rcases hpq with ⟨d, hdb, hd⟩
  have hb := mem_le hsb h
  refine ⟨orIntro s p q d, orIntro_le he hsb ?_ ?_ hdb, by simp, Derivation.orIntro h hd⟩
  · exact le_trans (le_of_lt (lt_or_left p q)) hb
  · exact le_trans (le_of_lt (lt_or_right p q)) hb

theorem all_m {s p : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (h : ^∀ p ∈ s)
    (hp : DerivableLe T (insert (free L p) (setShift L s)) (Exp.exp e)) :
    DerivableLe T s (Exp.exp (1024 * e)) := by
  rcases hp with ⟨d, hdb, hd⟩
  refine ⟨allIntro s p d, allIntro_le he hsb ?_ hdb, by simp, Derivation.allIntro h hd⟩
  exact le_trans (le_of_lt (lt_forall p)) (mem_le hsb h)

theorem ex_m {s p t : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (htb : t ≤ Exp.exp e)
    (h : ^∃ p ∈ s) (ht : IsTerm L t) (hp : DerivableLe T (insert (substs1 L t p) s) (Exp.exp e)) :
    DerivableLe T s (Exp.exp (1024 * e)) := by
  rcases hp with ⟨d, hdb, hd⟩
  refine ⟨exsIntro s p t d, exsIntro_le he hsb ?_ htb hdb, by simp, Derivation.exsIntro h ht hd⟩
  exact le_trans (le_of_lt (lt_exists p)) (mem_le hsb h)

theorem wk {s s' : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (hs : IsFormulaSet L s) (h : s' ⊆ s)
    (hd : DerivableLe T s' (Exp.exp e)) : DerivableLe T s (Exp.exp (1024 * e)) := by
  rcases hd with ⟨d, hdb, hd⟩
  exact ⟨wkRule s d, wkRule_le he hsb hdb, by simp, Derivation.wkRule hs h hd⟩

theorem shift {s : V} (he : 4 ≤ e) (hsb : setShift L s ≤ Exp.exp e)
    (hd : DerivableLe T s (Exp.exp e)) : DerivableLe T (setShift L s) (Exp.exp (1024 * e)) := by
  rcases hd with ⟨d, hdb, hd⟩
  exact ⟨shiftRule (setShift L s) d, shiftRule_le he hsb hdb, by simp, Derivation.shiftRule hd⟩

theorem cut {s : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (p : V) (hpb : p ≤ Exp.exp e)
    (hd₁ : DerivableLe T (insert p s) (Exp.exp e))
    (hd₂ : DerivableLe T (insert (neg L p) s) (Exp.exp e)) :
    DerivableLe T s (Exp.exp (1024 * e)) := by
  rcases hd₁ with ⟨d₁, hd₁b, hd₁⟩
  rcases hd₂ with ⟨d₂, hd₂b, hd₂⟩
  exact ⟨cutRule s p d₁ d₂, cutRule_le he hsb hpb hd₁b hd₂b, by simp, Derivation.cutRule hd₁ hd₂⟩

theorem by_axm {s : V} (he : 4 ≤ e) (hsb : s ≤ Exp.exp e) (hs : IsFormulaSet L s) (p : V)
    (hp : p ∈ s) (hT : p ∈ T.Δ₁Class) : DerivableLe T s (Exp.exp (1024 * e)) :=
  ⟨Bootstrapping.axm s p, axm_le he hsb (mem_le hsb hp), by simp, Derivation.axm hs hp hT⟩

/-! ### Derived rules with a member bound

These take a bound `B` on the members of the conclusion and derive the
sequent bounds for the intermediate weakenings themselves. -/

theorem insert_lt {x s B : V} (hx : x < B) (hs : ∀ y ∈ s, y < B) : ∀ y ∈ insert x s, y < B := by
  intro y hy
  rcases mem_bitInsert_iff.mp hy with rfl | hy
  · exact hx
  · exact hs y hy

theorem seq_le {s B e : V} (hBe : B ≤ e) (hs : ∀ y ∈ s, y < B) : s ≤ Exp.exp e :=
  le_trans (le_of_lt (seq_lt_exp hs)) (exp_monotone_le.mpr hBe)

theorem four_le_1024 {e : V} (he : 4 ≤ e) : 4 ≤ 1024 * e :=
  le_trans he (le_mul_of_one_le_left (Arithmetic.zero_le e) (by norm_num))

theorem le_1024 {e : V} : e ≤ 1024 * e :=
  le_mul_of_one_le_left (Arithmetic.zero_le e) (by norm_num)

/-- `Derivable.and` with sizes: `insert (p ⋏ q) s` from `insert p s` and `insert q s`. -/
theorem and {s p q B : V} (he : 4 ≤ e) (hBe : B ≤ e) (hs : ∀ y ∈ s, y < B) (hpqB : p ^⋏ q < B)
    (hp : DerivableLe T (insert p s) (Exp.exp e)) (hq : DerivableLe T (insert q s) (Exp.exp e)) :
    DerivableLe T (insert (p ^⋏ q) s) (Exp.exp (1024 * (1024 * e))) := by
  have hS := insert_lt hpqB hs
  have hpB : p < B := lt_trans (lt_K!_left p q) hpqB
  have hqB : q < B := lt_trans (lt_K!_right p q) hpqB
  refine and_m (four_le_1024 he) (le_exp_of_le (seq_le hBe hS) le_1024) (p := p) (q := q) (by simp) ?_ ?_
  · refine wk he (seq_le hBe (insert_lt hpB hS))
      (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) ?_ hp
    exact insert_subset_insert_of_subset _ (by simp)
  · refine wk he (seq_le hBe (insert_lt hqB hS))
      (by simp [hp.isFormulaSet.insert, hq.isFormulaSet.insert]) ?_ hq
    exact insert_subset_insert_of_subset _ (by simp)

/-- `Derivable.or` with sizes. -/
theorem or {s p q B : V} (he : 4 ≤ e) (hBe : B ≤ e) (hs : ∀ y ∈ s, y < B) (hpqB : p ^⋎ q < B)
    (hpq : DerivableLe T (insert p (insert q s)) (Exp.exp e)) :
    DerivableLe T (insert (p ^⋎ q) s) (Exp.exp (1024 * (1024 * e))) := by
  have hS := insert_lt hpqB hs
  have hpB : p < B := lt_trans (lt_or_left p q) hpqB
  have hqB : q < B := lt_trans (lt_or_right p q) hpqB
  refine or_m (four_le_1024 he) (le_exp_of_le (seq_le hBe hS) le_1024) (p := p) (q := q) (by simp) ?_
  refine wk he (seq_le hBe (insert_lt hpB (insert_lt hqB hS)))
    (by simp [hpq.isFormulaSet.insert, hpq.isFormulaSet.insert.2.insert]) ?_ hpq
  exact insert_subset_insert_of_subset _ (insert_subset_insert_of_subset _ (by simp))

end DerivableLe

end LeanProofs.BoundedPAConsistency.SizedDerivation
