module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationSyntax
public import M6PA.Calibration.PAForwardRelationalRewriting
@[expose] public section

/-! Typed relational syntax with separate bound and free environments. This is
not a numerical compiler or an arithmetic interpretation theorem. Internal
finite-environment encoding, source substitution with relational witnesses,
and arithmetic coherence remain separate obligations. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder
open RelationalSource
open Ordinal (Term Formula)

abbrev SourceTerm (n : Nat) := Semiterm Presentation.language Nat n
abbrev SourceFormula (n : Nat) := Semiformula Presentation.language Nat n

def shiftEnv {ι : Type} {m : Nat} (e : ι → Term m) : ι → Term (m+1) :=
  fun i => Rew.bShift (e i)

def bindEnv {n m : Nat} (b : Fin n → Term m) : Fin (n+1) → Term (m+1) :=
  Fin.cases (.bvar 0) (shiftEnv b)

/-- Each function occurrence receives actual existential value witnesses. -/
def value {n : Nat} : SourceTerm n → {m : Nat} →
    (Fin n → Term m) → (Nat → Term m) → Term m → Formula m
  | .bvar i, _, b, _, z => Ordinal.domain z ⋏ ND.eq z (b i)
  | .fvar i, _, _, f, z => Ordinal.domain z ⋏ ND.eq z (f i)
  | .func .zero _, _, _, _, z => Ordinal.domain z ⋏ Ordinal.zero z
  | .func .succ ts, _, b, f, z => Ordinal.domain z ⋏
      (∃¹ (value (ts 0) (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏
        Ordinal.successor (.bvar 0) (Rew.bShift z)))
  | .func .add ts, _, b, f, z => Ordinal.domain z ⋏
      (∃¹ ∃¹ (value (ts 0) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
        (value (ts 1) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
          PairGraph.addResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)))))
  | .func .mul ts, _, b, f, z => Ordinal.domain z ⋏
      (∃¹ ∃¹ (value (ts 0) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
        (value (ts 1) (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 0) ⋏
          PairGraph.mulResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)))))

/-- Arithmetic equality is order isomorphism between two actual values. -/
def equal {n m : Nat} (s t : SourceTerm n) (b : Fin n → Term m) (f : Nat → Term m) :
    Formula m :=
  ∃¹ ∃¹ (value s (shiftEnv (shiftEnv b)) (shiftEnv (shiftEnv f)) (.bvar 1) ⋏
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
  | _, .all p, _, b, f => ∀¹ (Ordinal.domain (.bvar 0) 🡒 formula p (bindEnv b) (shiftEnv f))
  | _, .exs p, _, b, f => ∃¹ (Ordinal.domain (.bvar 0) ⋏ formula p (bindEnv b) (shiftEnv f))

theorem value_env_ext {n m : Nat} (t : SourceTerm n)
    (b b' : Fin n → Term m) (f f' : Nat → Term m) (z : Term m)
    (hb : ∀ i, b i = b' i) (hf : ∀ i, f i = f' i) :
    value t b f z = value t b' f' z := by
  cases funext hb
  cases funext hf
  rfl

theorem formula_env_ext {n m : Nat} (p : SourceFormula n)
    (b b' : Fin n → Term m) (f f' : Nat → Term m)
    (hb : ∀ i, b i = b' i) (hf : ∀ i, f i = f' i) :
    formula p b f = formula p b' f' := by
  cases funext hb
  cases funext hf
  rfl

#print axioms value_env_ext
#print axioms formula_env_ext
end M6.PA.ForwardRelational

