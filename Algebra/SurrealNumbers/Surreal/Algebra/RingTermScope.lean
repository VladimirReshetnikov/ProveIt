import Surreal.Algebra.RingTermCodeComputability

/-!
# Effective scope checking for encoded ring terms

The bounded-variable prerequisite for formula coding in `odg:def:thm:saturation`.
A term is well scoped for `n` variables precisely when every variable index
is below `n`. This includes the empty variable context. Native `Fin n` terms
are equivalent to valid prefix streams passing the scope check.
-/

namespace Surreal.RingTermScope
open FirstOrder FirstOrder.Language RingTermCode

/-- The actual variable-scope condition on native terms. -/
def InScope (n : ℕ) : Language.ring.Term ℕ → Prop
  | .var k => k < n
  | .func _ ts => ∀ i, InScope n (ts i)

/-- Check one token's variable index; ring function tokens are always in scope. -/
def tokenScope (n : ℕ) : Token → Bool
  | .inl k => decide (k < n)
  | .inr _ => true

/-- Check every variable occurrence in a finite prefix stream. -/
def checkScope (n : ℕ) (l : List Token) : Bool :=
  l.foldr (fun t b => tokenScope n t && b) true

@[simp] theorem checkScope_nil (n : ℕ) : checkScope n [] = true := rfl
@[simp] theorem checkScope_cons (n : ℕ) (t : Token) (l : List Token) :
    checkScope n (t :: l) = (tokenScope n t && checkScope n l) := rfl

@[simp] theorem checkScope_append (n : ℕ) (l r : List Token) :
    checkScope n (l ++ r) = (checkScope n l && checkScope n r) := by
  induction l with
  | nil => simp
  | cons t l ih => simp [ih, Bool.and_assoc]

/-- The code-level check exactly matches the native term's scope condition. -/
theorem checkScope_encode (n : ℕ) (t : Language.ring.Term ℕ) :
    checkScope n (encode t) = true ↔ InScope n t := by
  induction t with
  | var k => simp [encode, tokenScope, InScope]
  | func f ts ih =>
    cases f <;> simp [encode, tokenScope, InScope, ih, Fin.forall_fin_succ]

/-- Forget the finite bound on variable indices. -/
def widen {n : ℕ} (t : Language.ring.Term (Fin n)) : Language.ring.Term ℕ := t.relabel Fin.val

/-- Restrict variable indices, replacing out-of-scope variables by the zero term.
For well-scoped inputs the replacement branch is never used. -/
def narrow (n : ℕ) : Language.ring.Term ℕ → Language.ring.Term (Fin n)
  | .var k => if h : k < n then .var ⟨k, h⟩ else 0
  | .func f ts => .func f (fun i => narrow n (ts i))

/-- Widening a bounded term always yields a well-scoped term. -/
theorem inScope_widen {n : ℕ} (t : Language.ring.Term (Fin n)) : InScope n (widen t) := by
  induction t with
  | var k => exact k.isLt
  | func f ts ih => exact ih

/-- Restriction is a left inverse to forgetting the variable bound. -/
@[simp] theorem narrow_widen {n : ℕ} (t : Language.ring.Term (Fin n)) :
    narrow n (widen t) = t := by
  induction t with
  | var k => simp [widen, Term.relabel, narrow]
  | func f ts ih =>
    change Term.func f (fun i => narrow n (widen (ts i))) = Term.func f ts
    congr 1
    exact funext ih

/-- On well-scoped terms restriction also has a right inverse. -/
theorem widen_narrow (n : ℕ) (t : Language.ring.Term ℕ) (h : InScope n t) :
    widen (narrow n t) = t := by
  induction t with
  | var k => simp only [InScope] at h; simp [narrow, h, widen, Term.relabel]
  | func f ts ih =>
    change Term.func f (fun i => widen (narrow n (ts i))) = Term.func f ts
    congr 1
    funext i
    exact ih i (h i)

/-- Codes for exactly one term whose variables lie in the specified finite context. -/
def Valid (n : ℕ) (l : List Token) : Prop := RingTermCode.Valid l ∧ checkScope n l = true

/-- Serialize a native term from a finite variable context. -/
def encode {n : ℕ} (t : Language.ring.Term (Fin n)) : List Token := RingTermCode.encode (widen t)

/-- Parse one term and check its scope before constructing a bounded native term. -/
def decode (n : ℕ) (l : List Token) : Option (Language.ring.Term (Fin n)) :=
  if checkScope n l then (RingTermCode.decode l).map (narrow n) else none

/-- Bounded native terms have valid scoped codes. -/
theorem valid_encode {n : ℕ} (t : Language.ring.Term (Fin n)) : Valid n (encode t) :=
  ⟨RingTermCode.valid_encode _, (checkScope_encode n _).mpr (inScope_widen t)⟩

/-- The scoped decoder recovers every bounded native term. -/
@[simp] theorem decode_encode {n : ℕ} (t : Language.ring.Term (Fin n)) :
    decode n (encode t) = some t := by
  rw [decode, if_pos (valid_encode t).2]
  simp only [encode, RingTermCode.decode_encode, Option.map_some, narrow_widen]

/-- Successful scoped decoding preserves the entire input stream. -/
theorem encode_of_decode {n : ℕ} {l : List Token} {t : Language.ring.Term (Fin n)}
    (h : decode n l = some t) : encode t = l := by
  unfold decode at h
  split at h
  · rename_i hs
    obtain ⟨u, hu, htu⟩ := Option.map_eq_some_iff.mp h
    subst t
    have he := RingTermCode.encode_of_decode hu
    have hi : InScope n u := (checkScope_encode n u).mp (he.symm ▸ hs)
    rw [encode, widen_narrow n u hi, he]
  · contradiction

/-- Validity describes exactly the successful scoped parses. -/
theorem valid_iff_decode (n : ℕ) (l : List Token) : Valid n l ↔ ∃ t, decode n l = some t := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨t, ht⟩ := (RingTermCode.valid_iff_decode l).mp hv
    exact ⟨narrow n t, by simp [decode, hs, ht]⟩
  · rintro ⟨t, ht⟩
    rw [← encode_of_decode ht]
    exact valid_encode t

/-- Finite-context native terms correspond exactly to valid scoped prefix streams. -/
def codeEquiv (n : ℕ) : Language.ring.Term (Fin n) ≃ {l : List Token // Valid n l} where
  toFun t := ⟨encode t, valid_encode t⟩
  invFun l := (decode n l.val).getD 0
  left_inv t := by simp
  right_inv l := by
    obtain ⟨t, ht⟩ := (valid_iff_decode n l.val).mp l.property
    apply Subtype.ext
    change encode ((decode n l.val).getD 0) = l.val
    rw [ht, Option.getD_some]
    exact encode_of_decode ht

end Surreal.RingTermScope
