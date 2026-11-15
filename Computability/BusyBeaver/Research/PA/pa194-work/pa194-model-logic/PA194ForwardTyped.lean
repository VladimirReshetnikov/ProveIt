import PA194BinaryTypedQuote
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ForwardTyped
open LO LO.FirstOrder
open M6.PA.RelationalSource
open Ordinal (Term Formula)
abbrev SourceTerm (n : Nat) := Semiterm PA194PAeq.language Nat n
abbrev SourceFormula (n : Nat) := Semiformula PA194PAeq.language Nat n
def shiftEnv {ι : Type} {m : Nat} (e : ι → Term m) : ι → Term (m+1) :=
  fun i => Rew.bShift (e i)
def bindEnv {n m : Nat} (b : Fin n → Term m) : Fin (n+1) → Term (m+1) :=
  Fin.cases (.bvar 0) (shiftEnv b)
def value {n : Nat} : SourceTerm n → {m : Nat} →
    (Fin n → Term m) → (Nat → Term m) → Term m → Formula m
  | .bvar i, _, b, _, z => Ordinal.domain z ⋏ ND.eq z (b i)
  | .fvar i, _, _, f, z => Ordinal.domain z ⋏ ND.eq z (f i)
  | .func .zero _, _, _, _, z => Ordinal.domain z ⋏ Ordinal.zero z
  | .func .succ ts, _, b, f, z => Ordinal.domain z ⋏
      (∃⁰ (value (ts 0) (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏
        Ordinal.successor (.bvar 0) (Rew.bShift z)))
  | .func .add ts, _, b, f, z => Ordinal.domain z ⋏
      (∃⁰ ∃⁰ (value (ts 0) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
        (value (ts 1) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
          PairGraph.addResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)))))
  | .func .mul ts, _, b, f, z => Ordinal.domain z ⋏
      (∃⁰ ∃⁰ (value (ts 0) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
        (value (ts 1) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
          PairGraph.mulResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)))))
def equal {n m : Nat} (s t : SourceTerm n) (b : Fin n → Term m) (f : Nat → Term m) : Formula m :=
  ∃⁰ ∃⁰ (value s (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
    (value t (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
      PairGraph.orderIso (.bvar 1) (.bvar 0)))
def formula : {n : Nat} → SourceFormula n → {m : Nat} →
    (Fin n → Term m) → (Nat → Term m) → Formula m
  | _, .verum, _, _, _ => .verum
  | _, .falsum, _, _, _ => .falsum
  | _, .rel .eq ts, _, b, f => equal (ts 0) (ts 1) b f
  | _, .nrel .eq ts, _, b, f => (equal (ts 0) (ts 1) b f).neg
  | _, .and p q, _, b, f => formula p b f ⋏ formula q b f
  | _, .or p q, _, b, f => formula p b f ⋎ formula q b f
  | _, .all p, _, b, f => ∀⁰ (sourceImply (Ordinal.domain (.bvar 0)) (formula p (bindEnv b) (shiftEnv f)))
  | _, .exs p, _, b, f => ∃⁰ (Ordinal.domain (.bvar 0) ⋏ formula p (bindEnv b) (shiftEnv f))
#print axioms value
#print axioms formula
end PA194ForwardTyped
