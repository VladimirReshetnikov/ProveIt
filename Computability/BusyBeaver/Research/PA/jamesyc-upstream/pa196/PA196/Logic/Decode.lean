module
public import PA196.Logic.Basic
@[expose] public section

/-! Total decoder for the PA196 codes. The universal constructor reads its
label from the *right* Cantor component, as the literal AX command requires.
Code zero is truth; code one is self-membership, not a built-in falsity atom.
-/
namespace PA196.Logic

inductive Named where
  | truth
  | imp (antecedent consequent : Named)
  | mem (container member : Nat)
  | eq (left right : Nat)
  | all (name : Nat) (body : Named)
  deriving DecidableEq

def Named.eval {V : Type u} (R : V → V → Prop) : Named → (Nat → V) → Prop
  | .truth,_ => True
  | .imp p q,env => p.eval R env → q.eval R env
  | .mem a b,env => R (env a) (env b)
  | .eq a b,env => env a = env b
  | .all a p,env => ∀ x, p.eval R (fun v => if v = a then x else env v)

namespace NumericDecode
open M6.Source.Cantor

def node (rec : Nat → Named) (n : Nat) : Named :=
  let a := (M6.Source.Cantor.decode (n / 4)).1
  let b := (M6.Source.Cantor.decode (n / 4)).2
  match n % 4 with
  | 0 => .imp (rec a) (rec b)
  | 1 => .mem a b
  | 2 => .all b (rec a)
  | _ => .eq a b

def fuel : Nat → Nat → Named
  | 0,_ => .truth
  | _+1,0 => .truth
  | k+1,n+1 => node (fuel k) (n+1)

def decode (n : Nat) := fuel (n+1) n

theorem unpair_bounds (n : Nat) :
    (M6.Source.Cantor.decode n).1 ≤ n ∧ (M6.Source.Cantor.decode n).2 ≤ n := by
  have h := pair_bounds (M6.Source.Cantor.decode n).1 (M6.Source.Cantor.decode n).2
  rwa [pair_decode] at h

theorem node_agree (rec other : Nat → Named) (n : Nat) (hn : 0 < n)
    (h : ∀ k < n, rec k = other k) : node rec n = node other n := by
  have hd : n/4 < n := Nat.div_lt_self hn (by decide)
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
    (4*pair a b+tag)/4 = pair a b ∧ (4*pair a b+tag)%4 = tag := by
  constructor <;> omega

theorem decode_zero : decode 0 = .truth := rfl
theorem decode_one : decode 1 = .mem 0 0 := rfl

theorem decode_mem (a b : Nat) : decode (wel a b) = .mem a b := by
  rw [unfold_decode _ (by simp [wel])]
  obtain ⟨hd,hm⟩ := tagged_fields a b 1 (by decide)
  simp only [wel,node,hd,hm,decode_pair]

theorem decode_eq (a b : Nat) : decode (weq a b) = .eq a b := by
  rw [unfold_decode _ (by simp [weq])]
  obtain ⟨hd,hm⟩ := tagged_fields a b 3 (by decide)
  simp only [weq,node,hd,hm,decode_pair]

theorem decode_all (a b : Nat) : decode (wal a b) = .all a (decode b) := by
  rw [unfold_decode _ (by simp [wal])]
  obtain ⟨hd,hm⟩ := tagged_fields b a 2 (by decide)
  simp only [wal,node,hd,hm,decode_pair]

theorem wim_positive (a b : Nat) (h : 0 < a+b) : 0 < wim a b := by
  have hp := pair_bounds a b
  simp only [wim]
  omega

theorem decode_imp (a b : Nat) (h : 0 < a+b) :
    decode (wim a b) = .imp (decode a) (decode b) := by
  rw [unfold_decode _ (wim_positive a b h)]
  obtain ⟨hd,hm⟩ := tagged_fields a b 0 (by decide)
  simp only [Nat.add_zero] at hd hm
  simp only [node,wim,hd,hm,decode_pair]
end NumericDecode

def Named.names (v : Nat) : Named → Bool
  | .truth => false
  | .imp p q => p.names v || q.names v
  | .mem a b | .eq a b => v == a || v == b
  | .all a p => v == a || p.names v

def Named.free (v : Nat) : Named → Bool
  | .truth => false
  | .imp p q => p.free v || q.free v
  | .mem a b | .eq a b => v == a || v == b
  | .all a p => !(v == a) && p.free v

theorem Named.free_in_names (p : Named) (v : Nat) (h : p.free v = true) :
    p.names v = true := by
  induction p with
  | truth => simp [free] at h
  | imp p q ihp ihq =>
    simp only [free,Bool.or_eq_true] at h
    simp only [names,Bool.or_eq_true]
    exact h.elim (fun hp => Or.inl (ihp hp)) (fun hq => Or.inr (ihq hq))
  | mem a b => exact h
  | eq a b => exact h
  | all a p ih =>
    simp only [free,Bool.and_eq_true] at h
    simp only [names,Bool.or_eq_true]
    exact Or.inr (ih h.2)

theorem NumericDecode.fuel_names_bound (k n v : Nat)
    (h : (NumericDecode.fuel k n).names v = true) : v < n := by
  induction k generalizing n with
  | zero => simp [NumericDecode.fuel,Named.names] at h
  | succ k ih =>
    cases n with
    | zero => simp [NumericDecode.fuel,Named.names] at h
    | succ n =>
      have hd : (n+1)/4 < n+1 := Nat.div_lt_self (by omega) (by decide)
      have hp := NumericDecode.unpair_bounds ((n+1)/4)
      simp only [NumericDecode.fuel,NumericDecode.node] at h
      split at h
      · simp only [Named.names,Bool.or_eq_true] at h
        rcases h with h | h <;> have hi := ih _ h <;> omega
      · simp only [Named.names,Bool.or_eq_true,beq_iff_eq] at h
        omega
      · simp only [Named.names,Bool.or_eq_true,beq_iff_eq] at h
        rcases h with h | h
        · omega
        · have hi := ih _ h; omega
      · simp only [Named.names,Bool.or_eq_true,beq_iff_eq] at h
        omega

theorem NumericDecode.self_fresh (n : Nat) : (NumericDecode.decode n).names n = false := by
  cases h : (NumericDecode.decode n).names n with
  | false => rfl
  | true =>
    have hb := NumericDecode.fuel_names_bound (n+1) n n h
    omega

theorem Named.eval_agree {V : Type u} (R : V → V → Prop) (p : Named)
    (env other : Nat → V) (h : ∀ v, p.free v = true → env v = other v) :
    p.eval R env ↔ p.eval R other := by
  induction p generalizing env other with
  | truth => rfl
  | mem a b =>
    have ha := h a (by simp [free])
    have hb := h b (by simp [free])
    simp only [eval,ha,hb]
  | eq a b =>
    have ha := h a (by simp [free])
    have hb := h b (by simp [free])
    simp only [eval,ha,hb]
  | imp p q ihp ihq =>
    have hp := ihp env other (fun v hv => h v (by simp [free,hv]))
    have hq := ihq env other (fun v hv => h v (by simp [free,hv]))
    simp only [eval,hp,hq]
  | all a p ih =>
    simp only [eval]
    apply forall_congr'
    intro x
    apply ih
    intro v hv
    by_cases hva : v = a
    · simp [hva]
    · simp only [hva,ite_false]
      apply h
      simp [free,hva,hv]

theorem Named.eval_fresh {V : Type u} (R : V → V → Prop) (p : Named)
    (env : Nat → V) (a : Nat) (x : V) (ha : p.free a = false) :
    p.eval R env ↔ p.eval R (fun v => if v = a then x else env v) := by
  apply p.eval_agree R
  intro v hv
  have hne : v ≠ a := by intro he; subst v; rw [ha] at hv; contradiction
  simp [hne]

#print axioms NumericDecode.decode_all
#print axioms NumericDecode.self_fresh
end PA196.Logic
