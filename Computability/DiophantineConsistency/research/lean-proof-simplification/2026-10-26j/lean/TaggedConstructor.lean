import Lean

/-!
Core-only proof of constructor discrimination on an arbitrary carrier.
The carrier can be a model of set theory; no decoding to external Nat
or enumeration of that model's elements is assumed.

The intended instance is tag = natV H and pair = kpair H. The production
normal-form equivalence for ObjectCodeBound.BoundStep is not proved here.
-/

namespace TaggedConstructor

structure Encoding (V : Type) where
  tag : Nat → V
  pair : V → V → V
  tag_injective : ∀ {m n}, tag m = tag n → m = n
  pair_injective : ∀ {a b c d}, pair a b = pair c d → a = c ∧ b = d

def tagged (E : Encoding V) (t : Nat) (payload : V) : V :=
  E.pair (E.tag t) payload

theorem tagged_eq_iff (E : Encoding V) (s t : Nat) (a b : V) :
    tagged E s a = tagged E t b ↔ s = t ∧ a = b := by
  constructor
  · intro h
    obtain ⟨ht, hp⟩ := E.pair_injective h
    exact ⟨E.tag_injective ht, hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def TaggedRel (E : Encoding V) (Allowed : Nat → Prop)
    (Local : Nat → V → W → Prop) (code : V) (result : W) : Prop :=
  ∃ t payload, Allowed t ∧ code = tagged E t payload ∧ Local t payload result

/-- One inversion theorem simultaneously removes tag alternatives and
transports the payload. It does not inspect an internal code recursively. -/
theorem taggedRel_at_constructor (E : Encoding V) (Allowed : Nat → Prop)
    (Local : Nat → V → W → Prop) (t : Nat) (payload : V) (result : W) :
    TaggedRel E Allowed Local (tagged E t payload) result ↔
      Allowed t ∧ Local t payload result := by
  constructor
  · rintro ⟨u, q, hu, hcode, hlocal⟩
    obtain ⟨ht, hp⟩ := (tagged_eq_iff E t u payload q).mp hcode
    subst u
    subst q
    exact ⟨hu, hlocal⟩
  · rintro ⟨ht, hlocal⟩
    exact ⟨t, payload, ht, rfl, hlocal⟩

#print axioms tagged_eq_iff
#print axioms taggedRel_at_constructor

end TaggedConstructor
