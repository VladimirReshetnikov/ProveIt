import BusyBeaver.ZFC.Code254Proof

/-!
An ordinary-Nat history evaluator for the exact twelve-rule C254 proof code.

The numeric row returns0 for invalid data and1+conclusion for a valid proof.
History contains values for codes0 throughn, in increasing order. Every child
read by the row is smaller than its parent. The final acceptance theorem covers
every natural input, including invalid trees; it is not just a quotation lemma.

This is an external executable construction, not a represented PA formula or
an internal totality theorem. The original calculus and coding are attributed
to Mira-Cult and Jeff as in the imported modules.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254History

open Code254 Code254Proof

/-- Distinguish an invalid tree from a valid proof of formula code0. -/
def parsedValue : Option RawProof → Nat
  | none => 0
  | some p => if p.valid then p.conclusion + 1 else 0

/-- One entirely numeric rule row. Recursive arguments are numeric values,
not decoded trees. The MP output is fielda, with childrenb andc. -/
def row (rec : Nat → Nat) (tag payload : Nat) : Nat :=
  let a := (Cantor.ofNat payload).1
  let tail := (Cantor.ofNat payload).2
  let b := (Cantor.ofNat tail).1
  let c := (Cantor.ofNat tail).2
  match tag with
  | 0 => if payload = 0 then 1 else 0
  | 1 =>
      let u := rec b
      let v := rec c
      if u = 0 ∨ v = 0 then 0
      else if v - 1 = wim (u - 1) a then a + 1 else 0
  | 2 => if rec tail = 0 then 0 else wal a (rec tail - 1) + 1
  | 3 => rho1 a tail + 1
  | 4 => rho2 a b c + 1
  | 5 => rho3 a b c + 1
  | 6 => rho4 a b c + 1
  | 7 => rho5 a b c + 1
  | 8 => rho6 a tail + 1
  | 9 => rho7 a b c + 1
  | 10 => rho8 a b (Cantor.ofNat c).1 (Cantor.ofNat c).2 + 1
  | 11 => if c ≠ a ∧ c ≠ b then Code254.bundle a b c + 1 else 0
  | _ => 0

/-- Compatibility with parsing and structural validation, at one rule. -/
theorem row_parsedValue (rec : Nat → Option RawProof) (tag payload : Nat) :
    row (fun c => parsedValue (rec c)) tag payload =
      parsedValue (decodeStep rec tag payload) := by
  match tag with
  | 0 =>
      by_cases hp : payload = 0 <;>
        simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion, hp]
  | 1 =>
      cases hp : rec (Cantor.ofNat (Cantor.ofNat payload).2).1 with
      | none => simp [row, decodeStep, hp, parsedValue]
      | some p =>
          cases hq : rec (Cantor.ofNat (Cantor.ofNat payload).2).2 with
          | none => simp [row, decodeStep, hp, hq, parsedValue]
          | some q =>
              cases hv : p.valid <;> cases hw : q.valid <;>
                simp [row, decodeStep, hp, hq, parsedValue, RawProof.valid,
                  RawProof.conclusion, hv, hw]
  | 2 =>
      cases hp : rec (Cantor.ofNat payload).2 with
      | none => simp [row, decodeStep, hp, parsedValue]
      | some p =>
          cases hv : p.valid <;>
            simp [row, decodeStep, hp, parsedValue, RawProof.valid, RawProof.conclusion, hv]
  | 3 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 4 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 5 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 6 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 7 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 8 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 9 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 10 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion]
  | 11 => simp [row, decodeStep, parsedValue, RawProof.valid, RawProof.conclusion,
               Bool.and_eq_true]
  | _ + 12 => rfl

/-- Only child indices at mostpayload can affect a rule. -/
theorem row_congr {f g : Nat → Nat} (tag payload : Nat)
    (h : ∀ i, i ≤ payload → f i = g i) : row f tag payload = row g tag payload := by
  have ht := (ofNat_le payload).2
  have hb := Nat.le_trans (ofNat_le (Cantor.ofNat payload).2).1 ht
  have hc := Nat.le_trans (ofNat_le (Cantor.ofNat payload).2).2 ht
  match tag with
  | 0 => rfl
  | 1 => simp only [row, h _ hb, h _ hc]
  | 2 => simp only [row, h _ ht]
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | _ + 12 => rfl

/-- Zero is invalid; positive codes use the exact base12 tag and payload. -/
def step (rec : Nat → Nat) : Nat → Nat
  | 0 => 0
  | z + 1 => row rec (z % 12) (z / 12)

/-- A numeric evaluator with an explicit depth budget, used to compare the
history construction with the existing parser. -/
def numericFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, c => step (numericFuel fuel) c

theorem numericFuel_parsedValue (fuel code : Nat) :
    numericFuel fuel code = parsedValue (decodeFuel fuel code) := by
  induction fuel generalizing code with
  | zero => rfl
  | succ fuel ih =>
      cases code with
      | zero => rfl
      | succ code =>
          simp only [numericFuel, step, decodeFuel]
          have he : numericFuel fuel = fun c => parsedValue (decodeFuel fuel c) := funext ih
          rw [he, row_parsedValue]

/-- Out-of-range history lookup is0. -/
def lookup (values : List Nat) (code : Nat) : Nat := values[code]?.getD 0

/-- The initial value at code0 is invalid. Each successor appends one code. -/
def history : Nat → List Nat
  | 0 => [0]
  | n + 1 => history n ++ [step (lookup (history n)) (n + 1)]

@[simp] theorem history_length (n : Nat) : (history n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history, ih]

private theorem lookup_append_left (values tail : List Nat) (code : Nat)
    (h : code < values.length) :
    lookup (values ++ tail) code = lookup values code := by
  simp [lookup, List.getElem?_append_left h]

private theorem lookup_append_last (values : List Nat) (value : Nat) :
    lookup (values ++ [value]) values.length = value := by
  simp [lookup]

/-- Every completed entry agrees with every parser fuel strictly above its
code. No assumption of validity, quotation or standard proof shape occurs. -/
theorem history_lookup (n code fuel : Nat) (hc : code ≤ n) (hf : code < fuel) :
    lookup (history n) code = numericFuel fuel code := by
  induction n generalizing code fuel with
  | zero =>
      have hcode : code = 0 := by omega
      subst code
      cases fuel with
      | zero => omega
      | succ fuel => rfl
  | succ n ih =>
      by_cases hsmall : code ≤ n
      · rw [history, lookup_append_left _ _ _ (by simp; omega)]
        exact ih code fuel hsmall hf
      · have hcode : code = n + 1 := by omega
        subst code
        cases fuel with
        | zero => omega
        | succ fuel =>
            have hlast : lookup (history (n + 1)) (n + 1) =
                step (lookup (history n)) (n + 1) := by
              rw [history]
              simpa only [history_length] using
                lookup_append_last (history n) (step (lookup (history n)) (n + 1))
            rw [hlast]
            simp only [numericFuel, step]
            apply row_congr
            intro i hi
            have hp : n / 12 ≤ n := Nat.div_le_self n 12
            exact ih i fuel (by omega) (by omega)

/-- The requested entry of the completed numeric history. -/
def value (code : Nat) : Nat := lookup (history code) code

theorem value_parsedValue (code : Nat) :
    value code = parsedValue (decodeFuel (code + 1) code) := by
  rw [value, history_lookup code code (code + 1) (Nat.le_refl _) (Nat.lt_succ_self _),
    numericFuel_parsedValue]

def accepts (code conclusion : Nat) : Bool := decide (value code = conclusion + 1)

/-- Exact acceptance agreement for ALL numeric inputs, including invalid
nodes, missing children, wrong MP formulas, and both gate collisions. -/
theorem accepts_iff_check (code conclusion : Nat) :
    accepts code conclusion = true ↔ Code254Proof.check code conclusion = true := by
  simp only [accepts, decide_eq_true_eq, value_parsedValue, Code254Proof.check]
  cases h : decodeFuel (code + 1) code with
  | none => simp [parsedValue]
  | some p =>
      cases hv : p.valid <;> simp [parsedValue, hv]

theorem c254_iff_history (conclusion : Nat) :
    C254 conclusion ↔ ∃ code, accepts code conclusion = true := by
  rw [c254_iff_checked]
  exact exists_congr fun code => (accepts_iff_check code conclusion).symm

end SetTheory.BusyBeaver.ZFC.Code254History
