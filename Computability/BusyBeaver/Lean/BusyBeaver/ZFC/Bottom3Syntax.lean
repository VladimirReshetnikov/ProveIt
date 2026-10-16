import BusyBeaver.ZFC.Base3Syntax

/-!
Primitive falsity in the ternary codec proposed by closure-kernel source 16
(arrival 9439d775aa).  Code 1 denotes Bottom and membership starts at 4.
The proofs adapt the existing Base3Syntax development; both codecs retain
code 0 as Truth and collapse Truth → Truth.  This module concerns syntax
and ordinary semantics, not proof search or binary-machine correctness.
-/
namespace SetTheory.BusyBeaver.ZFC.Bottom3Syntax
open Base3Syntax (pair pair_ofNat ofNat_pair sum_le_pair components_lt pack_div pack_mod)

inductive Formula where
  | truth
  | bottom
  | mem : Nat → Nat → Formula
  | imp : Formula → Formula → Formula
  | all : Nat → Formula → Formula
  deriving DecidableEq, Repr

def encode : Formula → Nat
  | .truth => 0
  | .bottom => 1
  | .mem i j => 3 * pair i j + 4
  | .imp p q => 3 * pair (encode p) (encode q)
  | .all i p => 3 * pair i (encode p) + 2

def Canonical : Formula → Prop
  | .truth => True
  | .bottom => True
  | .mem _ _ => True
  | .imp p q => Canonical p ∧ Canonical q ∧ (p ≠ .truth ∨ q ≠ .truth)
  | .all _ p => Canonical p

/-- Collapse the only constructor collision after canonicalizing children. -/
def smartImp (p q : Formula) : Formula :=
  if p = .truth ∧ q = .truth then .truth else .imp p q

theorem canonical_smartImp {p q : Formula} (hp : Canonical p) (hq : Canonical q) :
    Canonical (smartImp p q) := by
  unfold smartImp
  split
  · trivial
  · simp only [Canonical]
    refine ⟨hp, hq, ?_⟩
    rename_i h
    by_cases hp0 : p = .truth
    · exact Or.inr (fun hq0 => h ⟨hp0, hq0⟩)
    · exact Or.inl hp0

theorem encode_smartImp (p q : Formula) :
    encode (smartImp p q) = 3 * pair (encode p) (encode q) := by
  unfold smartImp
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    rfl
  · rfl

/-- Fuel is only a structural device: fuel greater than the input code suffices. -/
def decodeFuel : Nat → Nat → Formula
  | 0, _ => .truth
  | fuel + 1, n =>
      if n = 0 then .truth else if n = 1 then .bottom else
      let ab := Cantor.ofNat (n / 3)
      if n % 3 = 0 then .imp (decodeFuel fuel ab.1) (decodeFuel fuel ab.2)
      else if n % 3 = 1 then
        let ij := Cantor.ofNat ((n - 4) / 3)
        .mem ij.1 ij.2
      else .all ab.1 (decodeFuel fuel ab.2)

def decode (n : Nat) : Formula := decodeFuel (n + 1) n

theorem encode_decodeFuel (fuel n : Nat) (enough : n < fuel) :
    encode (decodeFuel fuel n) = n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hn : n = 0
      · subst n; simp [decodeFuel, encode]
      · by_cases hn1 : n = 1
        · subst n; simp [decodeFuel, encode]
        have hc := components_lt (Nat.pos_of_ne_zero hn)
        have hl := ih (Cantor.ofNat (n / 3)).1 (by omega)
        have hr := ih (Cantor.ofNat (n / 3)).2 (by omega)
        have hp := pair_ofNat (n / 3)
        have hpMem := pair_ofNat ((n - 4) / 3)
        simp only [decodeFuel, hn, hn1, if_false]
        split
        · simp only [encode, hl, hr]
          omega
        · split
          · simp only [encode]
            omega
          · simp only [encode, hr]
            have hm : n % 3 < 3 := Nat.mod_lt _ (by decide)
            omega

theorem encode_decode (n : Nat) : encode (decode n) = n :=
  encode_decodeFuel (n + 1) n (by omega)

theorem canonical_decodeFuel (fuel n : Nat) (enough : n < fuel) :
    Canonical (decodeFuel fuel n) := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hn : n = 0
      · subst n; simp [decodeFuel, Canonical]
      · by_cases hn1 : n = 1
        · subst n; simp [decodeFuel, Canonical]
        have hc := components_lt (Nat.pos_of_ne_zero hn)
        have hl := ih (Cantor.ofNat (n / 3)).1 (by omega)
        have hr := ih (Cantor.ofNat (n / 3)).2 (by omega)
        have el := encode_decodeFuel fuel (Cantor.ofNat (n / 3)).1 (by omega)
        have er := encode_decodeFuel fuel (Cantor.ofNat (n / 3)).2 (by omega)
        have hp := pair_ofNat (n / 3)
        simp only [decodeFuel, hn, hn1, if_false]
        split
        · rename_i hmod
          refine ⟨hl, hr, ?_⟩
          by_cases hleft : decodeFuel fuel (Cantor.ofNat (n / 3)).1 = .truth
          · by_cases hright : decodeFuel fuel (Cantor.ofNat (n / 3)).2 = .truth
            · rw [hleft] at el
              rw [hright] at er
              simp only [encode] at el er
              rw [← el, ← er] at hp
              change 0 = n / 3 at hp
              omega
            · exact Or.inr hright
          · exact Or.inl hleft
        · split
          · trivial
          · exact hr

theorem canonical_decode (n : Nat) : Canonical (decode n) :=
  canonical_decodeFuel (n + 1) n (by omega)

theorem encode_zero_iff {p : Formula} (canonical : Canonical p) :
    encode p = 0 ↔ p = .truth := by
  induction p with
  | truth => simp [encode]
  | bottom => simp [encode]
  | mem i j =>
      constructor
      · intro h; simp only [encode] at h; omega
      · intro h; cases h
  | imp p q hp hq =>
      rcases canonical with ⟨cp, cq, different⟩
      have hp0 := hp cp
      have hq0 := hq cq
      have hpair := sum_le_pair (encode p) (encode q)
      constructor
      · intro h
        exfalso
        simp only [encode] at h
        have ep : encode p = 0 := by omega
        have eq : encode q = 0 := by omega
        exact different.elim (fun h => h (hp0.mp ep)) (fun h => h (hq0.mp eq))
      · intro h; cases h
  | all i p hp =>
      constructor
      · intro h; simp only [encode] at h; omega
      · intro h; cases h

theorem decodeFuel_encode (p : Formula) (canonical : Canonical p)
    (fuel : Nat) (enough : encode p < fuel) : decodeFuel fuel (encode p) = p := by
  induction p generalizing fuel with
  | truth => cases fuel <;> simp_all [encode, decodeFuel]
  | bottom => cases fuel <;> simp_all [encode, decodeFuel]
  | mem i j =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hone : 3 * pair i j + 4 ≠ 1 := by omega
          have hmod : (3 * pair i j + 4) % 3 = 1 := by omega
          simp [encode, decodeFuel, hone, hmod, ofNat_pair]
  | imp p q hp hq =>
      rcases canonical with ⟨cp, cq, different⟩
      have hn : encode (.imp p q) ≠ 0 := by
        intro h
        have impossible := (encode_zero_iff (p := .imp p q) ⟨cp, cq, different⟩).mp h
        cases impossible
      have hpair := sum_le_pair (encode p) (encode q)
      cases fuel with
      | zero => omega
      | succ fuel =>
          have lp : encode p < fuel := by simp only [encode] at enough hn; omega
          have lq : encode q < fuel := by simp only [encode] at enough hn; omega
          have hd : (3 * pair (encode p) (encode q)) / 3 = pair (encode p) (encode q) := by omega
          have hm : (3 * pair (encode p) (encode q)) % 3 = 0 := by omega
          have hn1 : 3 * pair (encode p) (encode q) ≠ 1 := by omega
          simp only [encode] at hn
          simp [encode, decodeFuel, hn, hn1, hd, hm, ofNat_pair, hp cp fuel lp, hq cq fuel lq]
  | all i p hp =>
      have hpair := sum_le_pair i (encode p)
      cases fuel with
      | zero => omega
      | succ fuel =>
          have lp : encode p < fuel := by simp only [encode] at enough; omega
          have hn : 3 * pair i (encode p) + 2 ≠ 0 := by omega
          have hn1 : 3 * pair i (encode p) + 2 ≠ 1 := by omega
          simp [encode, decodeFuel, hn1,
                pack_div i (encode p) 2 (by decide), pack_mod i (encode p) 2 (by decide),
                ofNat_pair, hp canonical fuel lp]

theorem decode_encode (p : Formula) (canonical : Canonical p) : decode (encode p) = p :=
  decodeFuel_encode p canonical (encode p + 1) (by omega)

theorem encode_injective_on_canonical {p q : Formula}
    (hp : Canonical p) (hq : Canonical q) (h : encode p = encode q) : p = q := by
  have hd := congrArg decode h
  simpa only [decode_encode p hp, decode_encode q hq] using hd

theorem decode_imp_code (a b : Nat) :
    decode (3 * pair a b) = smartImp (decode a) (decode b) := by
  have hc := canonical_smartImp (canonical_decode a) (canonical_decode b)
  have hd := decode_encode (smartImp (decode a) (decode b)) hc
  simpa only [encode_smartImp, encode_decode] using hd

def labels : Formula → List Nat
  | .truth => []
  | .bottom => []
  | .mem i j => [i, j]
  | .imp p q => labels p ++ labels q
  | .all i p => i :: labels p

/-- This bound does not require canonical syntax; Truth has no labels. -/
theorem label_lt_encode (p : Formula) (i : Nat) (h : i ∈ labels p) : i < encode p := by
  induction p with
  | truth => simp [labels] at h
  | bottom => simp [labels] at h
  | mem a b =>
      have hp := sum_le_pair a b
      simp only [labels, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [encode]
      rcases h with h | h <;> omega
  | imp p q hp hq =>
      have hpair := sum_le_pair (encode p) (encode q)
      simp only [labels, List.mem_append] at h
      simp only [encode]
      rcases h with h | h
      · have hi := hp h; omega
      · have hi := hq h; omega
  | all a p hp =>
      have hpair := sum_le_pair a (encode p)
      simp only [labels, List.mem_cons] at h
      simp only [encode]
      rcases h with h | h
      · omega
      · have hi := hp h; omega

theorem decoded_label_lt (n i : Nat) (h : i ∈ labels (decode n)) : i < n := by
  have hi := label_lt_encode (decode n) i h
  simpa only [encode_decode] using hi

theorem code_fresh (n : Nat) : n ∉ labels (decode n) := by
  intro h
  have hi := decoded_label_lt n n h
  omega

/-- Normalize all children, contracting only Truth → Truth. -/
def normalize : Formula → Formula
  | .truth => .truth
  | .bottom => .bottom
  | .mem i j => .mem i j
  | .imp p q => smartImp (normalize p) (normalize q)
  | .all i p => .all i (normalize p)

theorem canonical_normalize (p : Formula) : Canonical (normalize p) := by
  induction p with
  | truth | bottom | mem => trivial
  | imp p q hp hq => exact canonical_smartImp hp hq
  | all i p hp => exact hp

theorem encode_normalize (p : Formula) : encode (normalize p) = encode p := by
  induction p with
  | truth | bottom | mem => rfl
  | imp p q hp hq => simp only [normalize, encode_smartImp, hp, hq, encode]
  | all i p hp => simp only [normalize, encode, hp]

/-- The formula round trip is total, not restricted to canonical inputs. -/
theorem decode_encode_normalize (p : Formula) : decode (encode p) = normalize p := by
  rw [← encode_normalize p]
  exact decode_encode (normalize p) (canonical_normalize p)

theorem normalize_idempotent (p : Formula) : normalize (normalize p) = normalize p := by
  rw [← decode_encode_normalize (normalize p), encode_normalize, decode_encode_normalize]

/-- Ordinary one-sorted semantics. No model of a reduced calculus is assumed. -/
def Sat {D : Type} (E : D → D → Prop) (v : Nat → D) : Formula → Prop
  | .truth => True
  | .bottom => False
  | .mem i j => E (v i) (v j)
  | .imp p q => Sat E v p → Sat E v q
  | .all i p => ∀ x, Sat E (fun j => if j = i then x else v j) p

theorem sat_smartImp {D : Type} (E : D → D → Prop) (v : Nat → D)
    (p q : Formula) : Sat E v (smartImp p q) ↔ (Sat E v p → Sat E v q) := by
  unfold smartImp
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    simp [Sat]
  · rfl

theorem sat_normalize {D : Type} (E : D → D → Prop) (v : Nat → D)
    (p : Formula) : Sat E v (normalize p) ↔ Sat E v p := by
  induction p generalizing v with
  | truth | bottom | mem => rfl
  | imp p q hp hq => simp only [normalize, sat_smartImp, Sat, hp, hq]
  | all i p hp => simp only [normalize, Sat, hp]

/-- Numerical canonicalization preserves the full ordinary formula meaning. -/
theorem sat_roundtrip {D : Type} (E : D → D → Prop) (v : Nat → D) (p : Formula) :
    Sat E v (decode (encode p)) ↔ Sat E v p := by
  rw [decode_encode_normalize]
  exact sat_normalize E v p

/-- Primitive Bottom has no variable that a quantifier can bind. -/
theorem sat_bottom {D : Type} (E : D → D → Prop) (v : Nat → D) :
    ¬ Sat E v (decode 1) := by
  change ¬ False
  exact id

theorem member_zero_code : encode (.mem 0 0) = 4 := rfl

/-- The emitter's code+2 wrapper is fresh for every matrix, including 0 and 1. -/
theorem wrapper_fresh (n : Nat) : n + 2 ∉ labels (decode n) := by
  intro h
  have hi := decoded_label_lt n (n + 2) h
  omega

#print axioms encode_decode
#print axioms decode_encode
#print axioms code_fresh
#print axioms decode_encode_normalize
#print axioms sat_roundtrip
#print axioms sat_bottom
#print axioms wrapper_fresh

end SetTheory.BusyBeaver.ZFC.Bottom3Syntax
