module
public import M6.Logic.NativeNamed
@[expose] public section

/-! Exact total decoder from NumericSyntax238.v:227ff, pinned by NativeCalculus.
The zero code is special. Tag-zero with consequent code1 is NNot, and code1
itself is NMem 0 0. Thus this is not an injective syntax serialization. -/
namespace M6.PA.NativeCalculus
namespace NumericDecode
open M6.Source.Cantor

def node (rec : Nat → Named) (n : Nat) : Named :=
  let a := (M6.Source.Cantor.decode (n / 4)).1
  let b := (M6.Source.Cantor.decode (n / 4)).2
  match n % 4 with
  | 0 => if b = 1 then .neg (rec a) else .imp (rec a) (rec b)
  | 1 => .mem a b
  | 2 => .all a (rec b)
  | _ => .eq a b

def fuel : Nat → Nat → Named
  | 0, _ => .truth
  | _ + 1, 0 => .truth
  | k + 1, n + 1 => node (fuel k) (n + 1)

def decode (n : Nat) := fuel (n+1) n

theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [triangle]; omega

theorem pair_bounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b := by
  have h := triangle_ge (a+b)
  simp only [pair]
  omega

theorem unpair_bounds (n : Nat) :
    (M6.Source.Cantor.decode n).1 ≤ n ∧ (M6.Source.Cantor.decode n).2 ≤ n := by
  have h := pair_bounds (M6.Source.Cantor.decode n).1 (M6.Source.Cantor.decode n).2
  rwa [pair_decode] at h

theorem node_agree (rec other : Nat → Named) (n : Nat) (hn : 0 < n)
    (h : ∀ k < n, rec k = other k) : node rec n = node other n := by
  have hd : n / 4 < n := Nat.div_lt_self hn (by decide)
  have hp := unpair_bounds (n/4)
  have ha := h (M6.Source.Cantor.decode (n/4)).1 (by omega)
  have hb := h (M6.Source.Cantor.decode (n/4)).2 (by omega)
  unfold node
  split <;> simp [ha,hb]

theorem fuel_stable (k j n : Nat) (hk : n < k) (hj : n < j) : fuel k n = fuel j n := by
  induction k generalizing j n with
  | zero => omega
  | succ k ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases n with
      | zero => rfl
      | succ n =>
        simp only [fuel]
        apply node_agree _ _ _ (by omega)
        intro m hm
        exact ih j m (by omega) (by omega)

theorem unfold_decode (n : Nat) (hn : 0 < n) : decode n = node decode n := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [decode,fuel]
    apply node_agree _ _ _ (by omega)
    intro m hm
    exact fuel_stable _ _ _ hm (by omega)

theorem tagged_fields (a b tag : Nat) (ht : tag < 4) :
    (4 * pair a b + tag) / 4 = pair a b ∧ (4 * pair a b + tag) % 4 = tag := by
  constructor <;> omega

theorem decode_zero : decode 0 = .truth := rfl

theorem decode_mem (a b : Nat) : decode (wel a b) = .mem a b := by
  rw [unfold_decode _ (by simp [wel])]
  obtain ⟨hd,hm⟩ := tagged_fields a b 1 (by decide)
  simp only [wel,node,hd,hm,decode_pair]

theorem decode_eq (a b : Nat) : decode (weq a b) = .eq a b := by
  rw [unfold_decode _ (by simp [weq])]
  obtain ⟨hd,hm⟩ := tagged_fields a b 3 (by decide)
  simp only [weq,node,hd,hm,decode_pair]

theorem decode_all (a b : Nat) : decode (wal a b) = .all a (decode b) := by
  rw [unfold_decode _ (by simp [wal,universal])]
  obtain ⟨hd,hm⟩ := tagged_fields a b 2 (by decide)
  simp only [wal,universal,node,hd,hm,decode_pair]

theorem wim_positive (a b : Nat) (h : 0 < a+b) : 0 < wim a b := by
  have hp := pair_bounds a b
  simp only [wim,implication]
  omega

theorem decode_imp (a b : Nat) (hb : b ≠ 1) (h : 0 < a+b) :
    decode (wim a b) = .imp (decode a) (decode b) := by
  rw [unfold_decode _ (wim_positive a b h)]
  obtain ⟨hd,hm⟩ := tagged_fields a b 0 (by decide)
  simp only [Nat.add_zero] at hd hm
  simp [node,wim,implication,hd,hm,decode_pair,hb]

theorem decode_neg (a : Nat) : decode (wn a) = .neg (decode a) := by
  rw [wn,unfold_decode _ (wim_positive a 1 (by omega))]
  obtain ⟨hd,hm⟩ := tagged_fields a 1 0 (by decide)
  simp only [Nat.add_zero] at hd hm
  simp [node,wim,implication,hd,hm,decode_pair]

theorem decode_one : decode 1 = .mem 0 0 := rfl

#print axioms fuel_stable
#print axioms decode_all
#print axioms decode_neg
end NumericDecode
end M6.PA.NativeCalculus

