module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLiftND
@[expose] public section

/-! The ordinary equality/membership language embeds into the unary-hole
language. This transports actual Foundation LK derivations, not semantic
validity or an assumed polymorphic predicate proof. -/
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder

def injection : RelationalSource.language →ᵥ sourceLanguage where
  func f := nomatch f
  rel r := match r with
    | .eq => .eq
    | .mem => .mem

abbrev liftTerm {n : Nat} (t : Semiterm RelationalSource.language Nat n) : Term n :=
  t.lMap injection
abbrev liftFormula {n : Nat} (p : Semiformula RelationalSource.language Nat n) : Formula n :=
  Semiformula.lMap injection p

def lowerTerm {n : Nat} : Term n → Semiterm RelationalSource.language Nat n
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .func f _ => nomatch f

@[simp] theorem lift_lowerTerm {n : Nat} (t : Term n) : liftTerm (lowerTerm t)=t := by
  cases t with
  | bvar i => rfl
  | fvar i => rfl
  | func f _ => nomatch f

@[simp] theorem lower_liftTerm {n : Nat} (t : Semiterm RelationalSource.language Nat n) :
    lowerTerm (liftTerm t)=t := by
  cases t with
  | bvar i => rfl
  | fvar i => rfl
  | func f _ => nomatch f

abbrev liftProof {Γ : LK.Sequent RelationalSource.language} (d : LK.Derivation Γ) :
    LK.Derivation (Γ.map liftFormula) := d.lMap injection

theorem negatives_lift (Γ : List RelationalSource.ND.Form) :
    ND.negatives (Γ.map liftFormula)=(RelationalSource.ND.negatives Γ).map liftFormula := by
  simp [ND.negatives,RelationalSource.ND.negatives,List.map_map,Function.comp_def,liftFormula,←Semiformula.neg_eq]

def liftND {Γ : List RelationalSource.ND.Form} {p : RelationalSource.ND.Form}
    (d : RelationalSource.ND.Proof Γ p) : ND.Proof (Γ.map liftFormula) (liftFormula p) :=
  (liftProof d).cast (by simp [ND.Proof,RelationalSource.ND.Proof,negatives_lift])

/-- Eliminate an explicit finite assumption list into any template context.
The supplied proofs may mention the unary predicate. -/
def ND.replaceContext {Γ Δ : List ND.Form} {p : ND.Form}
    (d : ND.Proof Γ p) (h : ∀q,q∈Γ→ND.Proof Δ q) : ND.Proof Δ p := by
  induction Γ generalizing p with
  | nil => exact ND.closed (d.cast (by simp [ND.negatives]))
  | cons q Γ ih =>
    exact ND.mp (h q (by simp)) (ih (ND.impIntro d) (fun r hr => h r (by simp [hr])))

def liftInto {Γ : List RelationalSource.ND.Form} {Δ : List ND.Form}
    {p : RelationalSource.ND.Form} (d : RelationalSource.ND.Proof Γ p)
    (h : ∀q,q∈Γ→ND.Proof Δ (liftFormula q)) : ND.Proof Δ (liftFormula p) := by
  induction Γ generalizing p with
  | nil => exact ND.closed ((liftND d).cast (by simp [ND.negatives]))
  | cons q Γ ih =>
    exact ND.mp (h q (by simp)) (by
      simpa [liftFormula] using (ih (RelationalSource.ND.impIntro d) (fun r hr => h r (by simp [hr]))))

#print axioms liftProof
#print axioms liftND
#print axioms ND.replaceContext
#print axioms liftInto
end M6.PA.RelationalPredicateTemplate
