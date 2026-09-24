/-
  ULTRAEXACTING CARDINALS: FAILURE OF DEFINABLE FINITE CHOICE (synthesis §9).

  The two theorems of §9 are proved here from the *exact list of facts about the
  embedding that their proofs use*.  Those facts (the cycles of Lemma 9.2, evaluation
  equivariance, `e(a) = e '' a` for countable `a`, preservation of the definable
  predicate) are consequences of elementarity established in reports R5 and R7; they
  appear as explicit hypotheses rather than being re-derived from a formal definition of
  ultraexactingness.  Nothing is admitted in this file.

  * `no_preserved_finite_family` — Theorem 9.4 (R5): no nonempty finite family of
    `r`-of-`n` selectors on the quotient is permuted by the embedding.
  * `no_finite_valued_transversal` — Theorem 9.10 (R7): a finite nonempty set of cofinal
    representatives cannot be mapped into itself.
  * `finiteChange_tail` — the invariance behind the finite-change cloud, Lemma 10.3 (R9).
-/
import Cardinals.Combinatorics.FiniteCycles
import Cardinals.Combinatorics.Ordinals

universe u

namespace Cardinals.Ultraexacting

open Finset

/-! ### Theorem 9.4: no preserved finite family of selectors -/

/-- **No preserved finite family (synthesis Theorem 9.4, second statement).**

* `Q` is the quotient `Q_λ`; `J` is the (injective) action of the witness `j` on the
  classes that lie in its domain;
* `cyc` is the cycle of Lemma 9.2: for the length `N = n * L` there are classes
  `q_0, …, q_{N-1}`, pairwise distinct, with `J (q_i) = q_{i+1}`;
* `Sel` is the finite family, `σ` the permutation induced by `j` (so `σ^[L] = id` for
  `L = lcm(1, …, |Sel|)` or `|Sel|!`), and `app f B = f(B)`;
* `hequiv` is evaluation under elementarity: `j(f)(j '' B) = j '' f(B)` for finite `B`.

Then the selectors cannot all choose exactly `r` of every `n` classes, `0 < r < n`. -/
theorem no_preserved_finite_family {Q Sel : Type*} [DecidableEq Q]
    (n r L : ℕ) (hr : 0 < r) (hrn : r < n) (hL : 0 < L)
    (J : Q → Q) (hJ : Function.Injective J)
    (cyc : ZMod (n * L) → Q) (hcyc_inj : Function.Injective cyc)
    (hcyc : ∀ i, J (cyc i) = cyc (i + 1))
    (σ : Sel → Sel) (hσ : ∀ f, σ^[L] f = f) (f₀ : Sel)
    (app : Sel → Finset Q → Finset Q)
    (hsel : ∀ f B, B.card = n → app f B ⊆ B ∧ (app f B).card = r)
    (hequiv : ∀ f B, app (σ f) (B.image J) = (app f B).image J) : False := by
  classical
  haveI : NeZero (n * L) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  -- pull the selectors back along the cycle
  let v : Sel → Finset (ZMod (n * L)) → Finset (ZMod (n * L)) := fun f B =>
    Finset.univ.filter (fun i => cyc i ∈ app f (B.image cyc))
  have himage : ∀ f B, B.card = n → (v f B).image cyc = app f (B.image cyc) := by
    intro f B hB
    have hsub := (hsel f (B.image cyc) (by rw [Finset.card_image_of_injective _ hcyc_inj, hB])).1
    ext q
    simp only [v, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hq
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (hsub hq)
      exact ⟨i, hq, rfl⟩
  have hJimage : ∀ B : Finset (ZMod (n * L)),
      (B.image (fun y => y + 1)).image cyc = (B.image cyc).image J := by
    intro B
    rw [Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro i _
    simp [Function.comp, hcyc]
  refine FiniteCycles.no_equivariant_selectors n r L hr hrn hL σ hσ f₀ v ?_ ?_
  · intro f B hB
    have h1 := hsel f (B.image cyc) (by rw [Finset.card_image_of_injective _ hcyc_inj, hB])
    refine ⟨?_, ?_⟩
    · intro i hi
      simp only [v, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨i', hi', hEq⟩ := Finset.mem_image.mp (h1.1 hi)
      exact hcyc_inj hEq ▸ hi'
    · rw [← Finset.card_image_of_injective _ hcyc_inj, himage f B hB]
      exact h1.2
  · intro f B
    ext i
    have hstep : cyc i = J (cyc (i - 1)) := by rw [hcyc]; congr 1; ring
    simp only [v, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hJimage, hequiv]
    constructor
    · intro hi
      obtain ⟨q', hq', hEq⟩ := Finset.mem_image.mp hi
      have hq'eq : q' = cyc (i - 1) := hJ (hEq.trans hstep)
      exact ⟨i - 1, hq'eq ▸ hq', by ring⟩
    · rintro ⟨i', hi', rfl⟩
      exact Finset.mem_image.mpr ⟨cyc i', hi', hcyc i'⟩

/-! ### Theorem 9.10: no finite-valued transversal -/

open Ordinal Set in
/-- Iterates of a map that preserves and is strictly increasing on `Iio lam`. -/
theorem iterate_facts (e : Ordinal.{u} → Ordinal.{u}) (lam : Ordinal.{u})
    (hlt : ∀ ξ < lam, e ξ < lam) (hmono : ∀ a b, a < b → b < lam → e a < e b) (k : ℕ) :
    (∀ ξ < lam, e^[k] ξ < lam) ∧ (∀ a b, a < b → b < lam → e^[k] a < e^[k] b) := by
  induction k with
  | zero => exact ⟨fun ξ hξ => hξ, fun a b hab _ => hab⟩
  | succ k ih =>
    refine ⟨fun ξ hξ => ?_, fun a b hab hb => ?_⟩
    · rw [Function.iterate_succ_apply']; exact hlt _ (ih.1 ξ hξ)
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hmono _ _ (ih.2 a b hab hb) (ih.1 b hb)

open Ordinal Set in
/-- **No finite-valued transversal (synthesis Theorem 9.10, report R7).**

`e` is the action on ordinals of an elementary `e : (V_{λ+1}, T) → (V_{λ+1}, T)`:
it maps `λ` into itself, is strictly increasing there, and moves every ordinal of
`[κ, λ)` upwards (Lemma 3.1).  `B = T ∩ [a]` is the finite nonempty set of selected
representatives of the class of the critical sequence; each is cofinal in `λ`, and
`b ↦ e '' b` maps `B` into itself (preservation of `T`, `e(a) =^* a`, and
`e(b) = e '' b` for countable `b`).  This is contradictory. -/
theorem no_finite_valued_transversal (e : Ordinal.{u} → Ordinal.{u}) (lam κ : Ordinal.{u})
    (hκ : κ < lam) (hlt : ∀ ξ < lam, e ξ < lam)
    (hmono : ∀ a b, a < b → b < lam → e a < e b)
    (hmove : ∀ ξ, κ ≤ ξ → ξ < lam → ξ < e ξ)
    (B : Finset (Set Ordinal.{u})) (hne : B.Nonempty)
    (hsub : ∀ b ∈ B, b ⊆ Iio lam) (hcof : ∀ b ∈ B, ∀ ξ < lam, ∃ x ∈ b, ξ ≤ x)
    (hmap : ∀ b ∈ B, e '' b ∈ B) : False := by
  classical
  -- `b ↦ e '' b` is an injective self-map of the finite set `B`
  have hinjOn : Set.InjOn e (Iio lam) := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with h | h | h
    · exact absurd hxy (ne_of_lt (hmono x y h hy))
    · exact h
    · exact absurd hxy.symm (ne_of_lt (hmono y x h hx))
  let g : B → B := fun b => ⟨e '' b.1, hmap b.1 b.2⟩
  have hg : Function.Injective g := by
    intro b b' hbb'
    have himg : e '' b.1 = e '' b'.1 := congrArg Subtype.val hbb'
    apply Subtype.ext
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := himg ▸ mem_image_of_mem e hx
      exact hinjOn (hsub _ b'.2 hy) (hsub _ b.2 hx) hyx ▸ hy
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := himg.symm ▸ mem_image_of_mem e hx
      exact hinjOn (hsub _ b.2 hy) (hsub _ b'.2 hx) hyx ▸ hy
  let π : Equiv.Perm B := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  have hp : 0 < orderOf π := orderOf_pos π
  -- some positive iterate fixes a representative
  obtain ⟨b₀, hb₀⟩ := hne
  have hfix : (g^[orderOf π]) ⟨b₀, hb₀⟩ = ⟨b₀, hb₀⟩ := by
    have h1 : π ^ orderOf π = 1 := pow_orderOf_eq_one π
    have h2 : (⇑π)^[orderOf π] = ⇑(π ^ orderOf π) := (Equiv.Perm.iterate_eq_pow π _)
    have : (⇑π)^[orderOf π] ⟨b₀, hb₀⟩ = ⟨b₀, hb₀⟩ := by rw [h2, h1]; rfl
    exact this
  have hiter : ∀ (k : ℕ) (b : B), ((g^[k]) b).1 = e^[k] '' b.1 := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply', Function.iterate_succ']
      show e '' ((g^[k]) b).1 = _
      rw [ih b, Set.image_image]
      rfl
  have himage : e^[orderOf π] '' b₀ = b₀ := by
    have := congrArg Subtype.val hfix
    rw [hiter] at this
    exact this
  obtain ⟨hlt', hmono'⟩ := iterate_facts e lam hlt hmono (orderOf π)
  have hsmono : StrictMonoOn (e^[orderOf π]) b₀ := fun x hx y hy hxy =>
    hmono' x y hxy (hsub b₀ hb₀ hy)
  have hid := OrdinalLemmas.strictMonoOn_image_eq_self (e^[orderOf π]) b₀ hsmono himage
  -- but a cofinal representative contains a point that every positive iterate moves
  obtain ⟨x, hxb, hκx⟩ := hcof b₀ hb₀ κ hκ
  have hxlam : x < lam := hsub b₀ hb₀ hxb
  have hgrow : ∀ k : ℕ, x ≤ e^[k] x ∧ e^[k] x < lam := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hxlam⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (hmove _ (hκx.trans ih.1) ih.2).le, hlt _ ih.2⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hlast : x < e^[orderOf π] x := by
    rw [hm, Function.iterate_succ_apply']
    exact lt_of_le_of_lt (hgrow m).1 (hmove _ (hκx.trans (hgrow m).1) (hgrow m).2)
  rw [hid x hxb] at hlast
  exact lt_irrefl _ hlast

/-! ### Lemma 10.3: the finite-change cloud is invariant under the tail shift -/

/-- Two sets of ordinals differ by finitely many points. -/
def FiniteChange (a b : Set Ordinal.{u}) : Prop := (symmDiff a b).Finite

theorem FiniteChange.symm {a b : Set Ordinal.{u}} (h : FiniteChange a b) : FiniteChange b a := by
  unfold FiniteChange at *; rwa [symmDiff_comm]

theorem FiniteChange.trans {a b c : Set Ordinal.{u}} (h₁ : FiniteChange a b)
    (h₂ : FiniteChange b c) : FiniteChange a c := by
  unfold FiniteChange at *
  exact (h₁.union h₂).subset (symmDiff_triangle a b c)

/-- The tail `c⁻ = ⟨c (n+1)⟩` of a sequence is a finite change of `c`. -/
theorem finiteChange_tail (c : ℕ → Ordinal.{u}) :
    FiniteChange (Set.range (fun n => c (n + 1))) (Set.range c) := by
  unfold FiniteChange
  apply (Set.finite_singleton (c 0)).subset
  intro x hx
  rcases hx with ⟨⟨n, rfl⟩, hnot⟩ | ⟨⟨n, rfl⟩, hnot⟩
  · exact absurd ⟨n + 1, rfl⟩ hnot
  · cases n with
    | zero => rfl
    | succ n => exact absurd ⟨n, rfl⟩ hnot

/-- **Shift invariance of the cloud (synthesis Lemma 10.3, last assertion).**  The family
of finite changes of the Prikry sequence is the same for the sequence and for its tail;
hence `e(Y_{τ,c}) = Y_{τ,c⁻} = Y_{τ,c}`. -/
theorem cloud_index_eq (c : ℕ → Ordinal.{u}) :
    {h : Set Ordinal.{u} | FiniteChange h (Set.range (fun n => c (n + 1)))} =
      {h : Set Ordinal.{u} | FiniteChange h (Set.range c)} := by
  ext h
  exact ⟨fun hh => hh.trans (finiteChange_tail c),
    fun hh => hh.trans (finiteChange_tail c).symm⟩

end Cardinals.Ultraexacting
