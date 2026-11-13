module
public import M6.Logic.NativeDecode
@[expose] public section

/-! Finite name tracking and freshness from the pinned NumericSyntax238.v.
This is the bounded-name component of future native readback/calibration. -/
namespace M6.PA.NativeCalculus
open M6.Source.Cantor

def Named.names (v : Nat) : Named → Bool
  | .truth => false
  | .imp p q => p.names v || q.names v
  | .neg p => p.names v
  | .mem a b | .eq a b => v == a || v == b
  | .all a p => v == a || p.names v

def Named.free (v : Nat) : Named → Bool
  | .truth => false
  | .imp p q => p.free v || q.free v
  | .neg p => p.free v
  | .mem a b | .eq a b => v == a || v == b
  | .all a p => !(v == a) && p.free v

def Named.binders (v : Nat) : Named → Bool
  | .truth | .mem _ _ | .eq _ _ => false
  | .imp p q => p.binders v || q.binders v
  | .neg p => p.binders v
  | .all a p => v == a || p.binders v

theorem Named.free_in_names (p : Named) (v : Nat) (h : p.free v = true) :
    p.names v = true := by
  induction p with
  | truth => simp [free] at h
  | imp p q ihp ihq =>
    simp only [free,Bool.or_eq_true] at h
    simp only [names,Bool.or_eq_true]
    exact h.elim (fun hp => Or.inl (ihp hp)) (fun hq => Or.inr (ihq hq))
  | neg p ih => exact ih h
  | mem a b => exact h
  | eq a b => exact h
  | all a p ih =>
    simp only [free,Bool.and_eq_true] at h
    simp only [names,Bool.or_eq_true]
    exact Or.inr (ih h.2)

theorem Named.binders_in_names (p : Named) (v : Nat) (h : p.binders v = true) :
    p.names v = true := by
  induction p with
  | truth => simp [binders] at h
  | mem a b => simp [binders] at h
  | eq a b => simp [binders] at h
  | imp p q ihp ihq =>
    simp only [binders,Bool.or_eq_true] at h
    simp only [names,Bool.or_eq_true]
    exact h.elim (fun hp => Or.inl (ihp hp)) (fun hq => Or.inr (ihq hq))
  | neg p ih => exact ih h
  | all a p ih =>
    simp only [binders,Bool.or_eq_true] at h
    simp only [names,Bool.or_eq_true]
    exact h.elim Or.inl (fun hp => Or.inr (ih hp))

theorem Named.names_bound (p : Named) (v : Nat) (h : p.names v = true) :
    v < p.encode := by
  induction p with
  | truth => simp [names] at h
  | imp p q ihp ihq =>
    have hp := NumericDecode.pair_bounds p.encode q.encode
    simp only [names,Bool.or_eq_true] at h
    simp only [encode,wim,implication]
    rcases h with h | h
    · have := ihp h; omega
    · have := ihq h; omega
  | neg p ih =>
    have hp := NumericDecode.pair_bounds p.encode 1
    have := ih h
    simp only [encode,wn,wim,implication]
    omega
  | mem a b =>
    have hp := NumericDecode.pair_bounds a b
    simp only [names,Bool.or_eq_true,beq_iff_eq] at h
    simp only [encode,wel]
    omega
  | eq a b =>
    have hp := NumericDecode.pair_bounds a b
    simp only [names,Bool.or_eq_true,beq_iff_eq] at h
    simp only [encode,weq]
    omega
  | all a p ih =>
    have hp := NumericDecode.pair_bounds a p.encode
    simp only [names,Bool.or_eq_true,beq_iff_eq] at h
    simp only [encode,wal,universal]
    rcases h with h | h
    · omega
    · have := ih h; omega

theorem Named.encoded_output_fresh (p : Named) : p.names p.encode = false := by
  cases h : p.names p.encode with
  | false => rfl
  | true => have := p.names_bound p.encode h; omega

theorem Named.encoded_output_free_fresh (p : Named) : p.free p.encode = false := by
  cases h : p.free p.encode with
  | false => rfl
  | true => have := p.free_in_names p.encode h; rw [p.encoded_output_fresh] at this; contradiction

theorem Named.encoded_output_binders_fresh (p : Named) : p.binders p.encode = false := by
  cases h : p.binders p.encode with
  | false => rfl
  | true => have := p.binders_in_names p.encode h; rw [p.encoded_output_fresh] at this; contradiction

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
      · split at h
        · have hi := ih _ h; omega
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

theorem Named.eval_agree {V : Type u} (R E : V → V → Prop) (p : Named)
    (env other : Nat → V) (h : ∀ v, p.free v = true → env v = other v) :
    p.eval R E env ↔ p.eval R E other := by
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
  | neg p ih => exact not_congr (ih env other h)
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

theorem Named.eval_fresh {V : Type u} (R E : V → V → Prop) (p : Named)
    (env : Nat → V) (a : Nat) (x : V) (ha : p.free a = false) :
    p.eval R E env ↔ p.eval R E (fun v => if v = a then x else env v) := by
  apply p.eval_agree R E
  intro v hv
  have hne : v ≠ a := by intro he; subst v; rw [ha] at hv; contradiction
  simp [hne]

#print axioms NumericDecode.self_fresh
#print axioms Named.eval_agree
#print axioms Named.names_bound
#print axioms Named.encoded_output_fresh
end M6.PA.NativeCalculus

