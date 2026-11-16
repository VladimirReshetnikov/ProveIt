module
public import M6PA.Calibration.NativeNamedInterpretation
public import M6PA.Theory
public import M6.Logic.NativeNames
@[expose] public section

/-! The logical source is Foundation's actual de-Bruijn Semiformula datatype
over an explicit empty-function membership/equality language, not a second
opaque provability predicate. `mem` has ordinary (member,container) ordering;
the named numeric calculus reverses it. No source-proof translation theorem
or PA/set interpretation is asserted by this syntax-only slice. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder NativeCalculus

inductive Relation : Nat → Type
  | eq : Relation 2
  | mem : Relation 2

def language : Language where
  Func := fun _ => Empty
  Rel := Relation

def termLabel {ξ : Type} {n : Nat} (t : Semiterm language ξ n)
    (bound : Fin n → Nat) (free : ξ → Nat) : Nat :=
  match t with
  | .bvar i => bound i
  | .fvar i => free i
  | .func f _ => nomatch f

def atomNamed {ξ : Type} {n k : Nat} (r : Relation k)
    (ts : Fin k → Semiterm language ξ n) (bound : Fin n → Nat) (free : ξ → Nat) : Named :=
  match r with
  | .eq => .eq (termLabel (ts 0) bound free) (termLabel (ts 1) bound free)
  | .mem => .mem (termLabel (ts 1) bound free) (termLabel (ts 0) bound free)

def toNamed {ξ : Type} : {n : Nat} → Semiformula language ξ n →
    (Fin n → Nat) → (ξ → Nat) → Nat → Named
  | _,.verum,_,_,_ => .truth
  | _,.falsum,_,_,_ => .mem 0 0
  | _,.rel r ts,b,f,_ => atomNamed r ts b f
  | _,.nrel r ts,b,f,_ => .neg (atomNamed r ts b f)
  | _,.and p q,b,f,lo => .neg (.imp (toNamed p b f lo) (.neg (toNamed q b f lo)))
  | _,.or p q,b,f,lo => .imp (.neg (toNamed p b f lo)) (toNamed q b f lo)
  | _,.all p,b,f,lo => .all lo (toNamed p (Fin.cases lo b) f (lo+1))
  | _,.exs p,b,f,lo => .neg (.all lo (.neg (toNamed p (Fin.cases lo b) f (lo+1))))

def depth {ξ : Type} {n : Nat} : Semiformula language ξ n → Nat
  | .verum | .falsum | .rel _ _ | .nrel _ _ => 0
  | .and p q | .or p q => max (depth p) (depth q)
  | .all p | .exs p => depth p + 1

theorem termLabel_lt {ξ : Type} {n : Nat} (t : Semiterm language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo : Nat)
    (hb : ∀ i,b i < lo) (hf : ∀ i,f i < lo) : termLabel t b f < lo := by
  cases t with
  | bvar i => exact hb i
  | fvar i => exact hf i
  | func fn _ => nomatch fn

theorem atom_names_lt {ξ : Type} {n k : Nat} (r : Relation k)
    (ts : Fin k → Semiterm language ξ n) (b : Fin n → Nat) (f : ξ → Nat)
    (lo v : Nat) (hb : ∀ i,b i < lo) (hf : ∀ i,f i < lo)
    (hv : (atomNamed r ts b f).names v = true) : v < lo := by
  cases r with
  | eq =>
    simp [atomNamed,Named.names] at hv
    rcases hv with rfl | rfl
    · exact termLabel_lt (ts 0) b f lo hb hf
    · exact termLabel_lt (ts 1) b f lo hb hf
  | mem =>
    simp [atomNamed,Named.names] at hv
    rcases hv with rfl | rfl
    · exact termLabel_lt (ts 1) b f lo hb hf
    · exact termLabel_lt (ts 0) b f lo hb hf

theorem toNamed_names_lt {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo v : Nat) (hlo : 0 < lo)
    (hb : ∀ i,b i < lo) (hf : ∀ i,f i < lo)
    (hv : (toNamed p b f lo).names v = true) : v < lo + depth p := by
  induction p generalizing lo with
  | verum => simp [toNamed,Named.names] at hv
  | falsum =>
    simp [toNamed,Named.names] at hv
    subst v
    simpa [depth] using hlo
  | rel r ts | nrel r ts =>
    simpa [depth] using atom_names_lt r ts b f lo v hb hf hv
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [toNamed,Named.names,Bool.or_eq_true] at hv
    rcases hv with hv | hv
    · have h := ihp b lo hlo hb hf hv
      simp only [depth]; omega
    · have h := ihq b lo hlo hb hf hv
      simp only [depth]; omega
  | all p ih | exs p ih =>
    simp only [toNamed,Named.names,Bool.or_eq_true,beq_iff_eq] at hv
    rcases hv with rfl | hv
    · simp only [depth]; omega
    · have hb' : ∀ i, (Fin.cases (motive := fun _ => Nat) lo b) i < lo+1 := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simpa using Nat.lt_trans (hb j) (Nat.lt_succ_self lo)
      have hf' : ∀ i, f i < lo+1 := fun i => Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
      have h := ih (Fin.cases lo b) (lo+1) (by omega) hb' hf' hv
      simp only [depth]; omega

theorem toNamed_reserved {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo z : Nat) (hlo : 0 < lo)
    (hb : ∀ i,b i < lo) (hf : ∀ i,f i < lo) (hz : lo + depth p ≤ z) :
    (toNamed p b f lo).names z = false := by
  cases he : (toNamed p b f lo).names z with
  | false => rfl
  | true => have h := toNamed_names_lt p b f lo z hlo hb hf he; omega

theorem termLabel_bShift {ξ : Type} {n : Nat} (t : Semiterm language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (fresh : Nat) :
    termLabel (Rew.bShift t) (Fin.cases fresh b) f = termLabel t b f := by
  cases t with
  | bvar i => rfl
  | fvar i => rfl
  | func fn _ => nomatch fn

#print axioms toNamed_reserved
#print axioms termLabel_bShift
end M6.PA.RelationalSource

