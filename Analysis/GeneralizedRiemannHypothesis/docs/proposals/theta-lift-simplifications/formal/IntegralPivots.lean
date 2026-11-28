import Std

/-!
# Integral coordinates from unit pivots

`Integral` is a scalar predicate closed under zero, addition, multiplication,
and subtraction. The index type `X` can be any set of scalar evaluations.
`expand` forms an actual finite linear combination of the columns `b`.
-/

namespace IntegralPivots

open Lean.Grind

universe u v
variable {K : Type u} [CommRing K] {X : Type v}

def expand : (n : Nat) → (Fin n → X → K) → (Fin n → K) → X → K
  | 0, _, _, _ => 0
  | n + 1, b, c, x => b 0 x * c 0 + expand n (fun i => b i.succ) (fun i => c i.succ) x

structure Closed (I : K → Prop) : Prop where
  zero : I 0
  add : ∀ {a b}, I a → I b → I (a+b)
  mul : ∀ {a b}, I a → I b → I (a*b)
  sub : ∀ {a b}, I a → I b → I (a-b)

/-- Later columns vanish at every earlier pivot. -/
structure UnitPivots {n : Nat} (b : Fin n → X → K) (p : Fin n → X) : Prop where
  unit : ∀ i, b i (p i) = 1
  later : ∀ i j, i < j → b j (p i) = 0

private theorem eval_zero {n} (b : Fin n → X → K) (c : Fin n → K)
    (x : X) (h : ∀ i, b i x = 0) : expand n b c x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := ih (fun i => b i.succ) (fun i => c i.succ) (fun i => h i.succ)
    simp only [expand, h 0, Semiring.zero_mul, ht, Semiring.add_zero]

/-- A vector in the span of integral unit-pivot columns is pointwise integral
exactly when all its given coefficients are integral. -/
theorem integral_expand_iff {n : Nat} (I : K → Prop) (hI : Closed I)
    (b : Fin n → X → K) (p : Fin n → X) (c : Fin n → K)
    (hb : ∀ i x, I (b i x)) (hp : UnitPivots b p) :
    (∀ x, I (expand n b c x)) ↔ ∀ i, I (c i) := by
  induction n with
  | zero => exact ⟨fun _ i => Fin.elim0 i, fun _ _ => hI.zero⟩
  | succ n ih =>
    let b' : Fin n → X → K := fun i => b i.succ
    let c' : Fin n → K := fun i => c i.succ
    let p' : Fin n → X := fun i => p i.succ
    have hp' : UnitPivots b' p' :=
      ⟨fun i => hp.unit i.succ, fun i j hij => hp.later i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩
    have smaller := ih b' p' c' (fun i => hb i.succ) hp'
    constructor
    · intro hx
      have hz := eval_zero b' c' (p 0)
        (fun i => hp.later 0 i.succ (Nat.zero_lt_succ i.val))
      have h0 := hx (p 0)
      change I (b 0 (p 0) * c 0 + expand n b' c' (p 0)) at h0
      rw [hz, hp.unit 0, Semiring.one_mul, Semiring.add_zero] at h0
      have tail (x : X) : I (expand n b' c' x) := by
        have hfull := hx x
        change I (b 0 x * c 0 + expand n b' c' x) at hfull
        have h := hI.sub hfull (hI.mul (hb 0 x) h0)
        have heq : b 0 x * c 0 + expand n b' c' x - b 0 x * c 0 = expand n b' c' x := by grind
        rwa [heq] at h
      exact Fin.cases h0 (smaller.mp tail)
    · intro hc x
      exact hI.add (hI.mul (hb 0 x) (hc 0)) (smaller.mpr (fun i => hc i.succ) x)

/-- A nonempty finite list of evaluations attains a maximum for every total
transitive comparison (in applications, comparison of nonarchimedean norms). -/
theorem finite_max {α : Type u} (le : α → α → Prop)
    (total : ∀ a b, le a b ∨ le b a) (trans : ∀ {a b c}, le a b → le b c → le a c)
    (m : Nat) (v : Fin (m+1) → α) : ∃ p, ∀ i, le (v i) (v p) := by
  induction m with
  | zero =>
    refine ⟨0, fun i => ?_⟩
    have hi : i = 0 := Fin.ext (by omega)
    rw [hi]
    exact (total _ _).elim id id
  | succ m ih =>
    obtain ⟨p,hp⟩ := ih (fun i => v i.succ)
    rcases total (v 0) (v p.succ) with h | h
    · exact ⟨p.succ, Fin.cases h hp⟩
    · exact ⟨0, Fin.cases ((total _ _).elim id id) (fun i => trans (hp i) h)⟩

/-- Eliminate all pivot coordinates from an arbitrary evaluation vector. The
subtracted linear combination and the residual are returned together. -/
theorem eliminate {n : Nat} (b : Fin n → X → K) (p : Fin n → X)
    (hp : UnitPivots b p) (v : X → K) :
    ∃ (c : Fin n → K) (w : X → K),
      (∀ x, v x = expand n b c x + w x) ∧ (∀ i, w (p i) = 0) := by
  induction n generalizing v with
  | zero =>
    exact ⟨Fin.elim0, v, fun x => by change v x = 0 + v x; grind,
      fun i => Fin.elim0 i⟩
  | succ n ih =>
    let bs : Fin n → X → K := fun i => b i.succ
    let ps : Fin n → X := fun i => p i.succ
    have hps : UnitPivots bs ps :=
      ⟨fun i => hp.unit i.succ, fun i j hij => hp.later i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)⟩
    let v' : X → K := fun x => v x - b 0 x * v (p 0)
    obtain ⟨d,w,hs,hw⟩ := ih bs ps hps v'
    let c : Fin (n+1) → K := Fin.cases (v (p 0)) d
    have hs' (x : X) : v x - b 0 x * v (p 0) = expand n bs d x + w x := hs x
    refine ⟨c,w,?_,Fin.cases ?_ hw⟩
    · intro x
      simp only [expand, c, Fin.cases_zero, Fin.cases_succ]
      change v x = b 0 x * v (p 0) + expand n bs d x + w x
      grind [hs' x]
    · have hz := eval_zero bs d (p 0) (fun i => hp.later 0 i.succ (Nat.zero_lt_succ i.val))
      have h := hs' (p 0)
      rw [hp.unit 0, Semiring.one_mul, hz] at h
      grind

/-- Divisibility with an integral quotient; this is a total preorder in a
valuation field. Only multiplication enters the proof of transitivity. -/
def dominates (I : K → Prop) (a b : K) : Prop := ∃ c, I c ∧ a = b*c

/-- Extend an integral echelon flag by an arbitrary vector outside its span.
The new column is integral at every evaluation, vanishes at all previous
pivots and takes value one at its own pivot. The returned equation expresses
the original vector in the extended flag with a nonzero new coefficient.

The added finite-dimensional input is only the finite set of evaluations.
The totality hypothesis is the defining divisibility property of a valuation
ring on the coefficient field. No discrete value group is used.
-/
theorem extend_flag {F : Type u} [Field F] (I : F → Prop) (hI : Closed I)
    (comparable : ∀ a b, dominates I a b ∨ dominates I b a)
    {n m : Nat} (b : Fin n → Fin (m+1) → F) (p : Fin n → Fin (m+1))
    (hp : UnitPivots b p) (v : Fin (m+1) → F)
    (outside : ¬∃ c, ∀ x, v x = expand n b c x) :
    ∃ (q : Fin (m+1)) (w : Fin (m+1) → F) (s : F) (c : Fin n → F),
      s ≠ 0 ∧ (∀ x, I (w x)) ∧ w q = 1 ∧ (∀ i, w (p i) = 0) ∧
      (∀ x, v x = expand n b c x + s * w x) := by
  classical
  obtain ⟨c,t,ht,hz⟩ := eliminate b p hp v
  have trans {a b' d : F} (hab : dominates I a b') (hbd : dominates I b' d) : dominates I a d := by
    obtain ⟨s,hs,h1⟩ := hab
    obtain ⟨u,hu,h2⟩ := hbd
    exact ⟨u*s, hI.mul hu hs, by rw [h1,h2,Semiring.mul_assoc]⟩
  obtain ⟨q,hq⟩ := finite_max (dominates I) comparable trans m t
  let w (i : Fin (m+1)) := Classical.choose (hq i)
  have hw (i : Fin (m+1)) : I (w i) := (Classical.choose_spec (hq i)).1
  have heq (i : Fin (m+1)) : t i = t q * w i := (Classical.choose_spec (hq i)).2
  have hne : t q ≠ 0 := by
    intro hzero
    apply outside
    refine ⟨c,fun x => ?_⟩
    have hx := heq x
    rw [hzero, Semiring.zero_mul] at hx
    rw [ht x, hx, Semiring.add_zero]
  have hinv := Field.inv_mul_cancel hne
  have cancel (x : F) : (t q)⁻¹ * (t q * x) = x := by
    rw [← Semiring.mul_assoc, hinv, Semiring.one_mul]
  refine ⟨q,w,t q,c,hne,hw,?_,?_,fun x => (ht x).trans (by rw [← heq x])⟩
  · have h := congrArg (fun z => (t q)⁻¹ * z) (heq q)
    change (t q)⁻¹ * t q = (t q)⁻¹ * (t q * w q) at h
    rw [cancel, hinv] at h
    exact h.symm
  · intro i
    have h := congrArg (fun z => (t q)⁻¹ * z) (heq (p i))
    change (t q)⁻¹ * t (p i) = (t q)⁻¹ * (t q * w (p i)) at h
    rw [cancel, hz, Semiring.mul_zero] at h
    exact h.symm

/-- Append a last entry, keeping the previous index order. -/
def snoc {α : Type u} {n : Nat} (a : Fin n → α) (last : α) : Fin (n+1) → α :=
  Fin.lastCases last a

/-- The appended unit pivot supplies an echelon family for the next step. -/
theorem append_unitPivots {n} (b : Fin n → X → K) (p : Fin n → X)
    (hp : UnitPivots b p) (w : X → K) (q : X)
    (one : w q = 1) (vanish : ∀ i, w (p i) = 0) :
    UnitPivots (snoc b w) (snoc p q) := by
  constructor
  · intro i
    induction i using Fin.lastCases with
    | last => simpa [snoc] using one
    | cast i => simpa [snoc] using hp.unit i
  · intro i j
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => intro h; exact False.elim (Nat.lt_irrefl _ h)
      | cast i => intro _; simpa [snoc] using vanish i
    | cast j =>
      induction i using Fin.lastCases with
      | last =>
        intro h
        have : n < j.val := h
        omega
      | cast i => intro h; simpa [snoc] using hp.later i j (Fin.castSucc_lt_castSucc_iff.mp h)

end IntegralPivots

#print axioms IntegralPivots.integral_expand_iff
#print axioms IntegralPivots.finite_max

#print axioms IntegralPivots.extend_flag

#print axioms IntegralPivots.append_unitPivots
