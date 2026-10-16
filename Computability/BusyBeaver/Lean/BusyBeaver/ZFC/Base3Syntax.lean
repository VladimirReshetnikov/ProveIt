import FirstOrder.Fol
import BusyBeaver.ZFC.Base3Encoding

/-!
The numerical base-3 codec, including the runtime's code0 truth alias.

Every natural has a finite canonical decode.  Implication of Truth by Truth
is normalized to Truth: both otherwise have code0.  This is a numerical syntax
theorem, not a calculus, semantic interpretation, compiler simulation or ZFC
equiconsistency proof.  In particular Truth here does not assert anything
about the separate runtime relative-falsity atom Rel(0,0).
-/

namespace SetTheory.BusyBeaver.ZFC.Base3Syntax

abbrev pair := Base3Encoding.pair

theorem triangle_eq_cantor (n : Nat) : Base3Encoding.triangle n = Cantor.tri n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Base3Encoding.triangle, Cantor.tri, ih, Nat.add_assoc]

theorem pair_eq_cantor (a b : Nat) : pair a b = Cantor.toNat (a, b) := by
  simp [pair, Base3Encoding.pair, Cantor.toNat, triangle_eq_cantor, Nat.add_comm]

theorem pair_ofNat (n : Nat) :
    pair (Cantor.ofNat n).1 (Cantor.ofNat n).2 = n := by
  rw [pair_eq_cantor]
  exact Cantor.toNat_ofNat n

theorem ofNat_pair (a b : Nat) : Cantor.ofNat (pair a b) = (a, b) := by
  rw [pair_eq_cantor]
  exact Cantor.ofNat_toNat (a, b)

theorem sum_le_pair (a b : Nat) : a + b ≤ pair a b :=
  Base3Encoding.sum_le_pair a b

theorem components_lt {n : Nat} (positive : 0 < n) :
    (Cantor.ofNat (n / 3)).1 < n ∧ (Cantor.ofNat (n / 3)).2 < n := by
  have hp := sum_le_pair (Cantor.ofNat (n / 3)).1
    (Cantor.ofNat (n / 3)).2
  rw [pair_ofNat] at hp
  omega

theorem pack_div (a b tag : Nat) (small : tag < 3) :
    (3 * pair a b + tag) / 3 = pair a b := by omega

theorem pack_mod (a b tag : Nat) (small : tag < 3) :
    (3 * pair a b + tag) % 3 = tag := by omega

inductive Formula where
  | truth
  | mem : Nat → Nat → Formula
  | imp : Formula → Formula → Formula
  | all : Nat → Formula → Formula
  deriving DecidableEq, Repr

def encode : Formula → Nat
  | .truth => 0
  | .mem i j => 3 * pair i j + 1
  | .imp p q => 3 * pair (encode p) (encode q)
  | .all i p => 3 * pair i (encode p) + 2

def Canonical : Formula → Prop
  | .truth => True
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
      if n = 0 then .truth else
      let ab := Cantor.ofNat (n / 3)
      if n % 3 = 0 then .imp (decodeFuel fuel ab.1) (decodeFuel fuel ab.2)
      else if n % 3 = 1 then .mem ab.1 ab.2
      else .all ab.1 (decodeFuel fuel ab.2)

def decode (n : Nat) : Formula := decodeFuel (n + 1) n

theorem encode_decodeFuel (fuel n : Nat) (enough : n < fuel) :
    encode (decodeFuel fuel n) = n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
      by_cases hn : n = 0
      · subst n; simp [decodeFuel, encode]
      · have hc := components_lt (Nat.pos_of_ne_zero hn)
        have hl := ih (Cantor.ofNat (n / 3)).1 (by omega)
        have hr := ih (Cantor.ofNat (n / 3)).2 (by omega)
        have hp := pair_ofNat (n / 3)
        simp only [decodeFuel, hn, if_false]
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
      · have hc := components_lt (Nat.pos_of_ne_zero hn)
        have hl := ih (Cantor.ofNat (n / 3)).1 (by omega)
        have hr := ih (Cantor.ofNat (n / 3)).2 (by omega)
        have el := encode_decodeFuel fuel (Cantor.ofNat (n / 3)).1 (by omega)
        have er := encode_decodeFuel fuel (Cantor.ofNat (n / 3)).2 (by omega)
        have hp := pair_ofNat (n / 3)
        simp only [decodeFuel, hn, if_false]
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
  | mem i j =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hn : 3 * pair i j + 1 ≠ 0 := by omega
          simp only [encode, decodeFuel, hn, if_false,
                     pack_div i j 1 (by decide), pack_mod i j 1 (by decide),
                     ofNat_pair]
          rfl
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
          simp only [encode] at hn
          simp [encode, decodeFuel, hn, hd, hm, ofNat_pair, hp cp fuel lp, hq cq fuel lq]
  | all i p hp =>
      have hpair := sum_le_pair i (encode p)
      cases fuel with
      | zero => omega
      | succ fuel =>
          have lp : encode p < fuel := by simp only [encode] at enough; omega
          have hn : 3 * pair i (encode p) + 2 ≠ 0 := by omega
          simp [encode, decodeFuel,
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
  | .mem i j => [i, j]
  | .imp p q => labels p ++ labels q
  | .all i p => i :: labels p

/-- This bound does not require canonical syntax; Truth has no labels. -/
theorem label_lt_encode (p : Formula) (i : Nat) (h : i ∈ labels p) : i < encode p := by
  induction p with
  | truth => simp [labels] at h
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

#print axioms encode_decode
#print axioms decode_encode
#print axioms code_fresh

end SetTheory.BusyBeaver.ZFC.Base3Syntax
