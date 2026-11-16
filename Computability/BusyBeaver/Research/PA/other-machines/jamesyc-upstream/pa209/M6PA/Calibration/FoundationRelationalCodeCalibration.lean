module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeRecursion
@[expose] public section

/-! Standard syntax calibration to the unchanged external interpretation.
Environments are explicitly the total lookups of finite HFS vectors; no arbitrary
host function is assumed to have a finite representation. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualArithmeticGraph ActualHeadGraphs
open NativeCalculus NativeCalculus.ActualBasis

/-- This is an explicit lookup function, including the documented nth default. -/
noncomputable def boundLookup {n : Nat} (b : Nat) (i : Fin n) : Nat := nth b (i:Nat)
noncomputable def freeLookup (f i : Nat) : Nat := nth f i

theorem totalLabel_quote {n : Nat} (t : SyntacticSemiterm language n) (b f : Nat) :
    totalLabel (⌜t⌝ : Nat) b f=termLabel t (boundLookup b) (freeLookup f) := by
  cases t with
  | bvar i => simp [boundLookup,termLabel]
  | fvar i => simp [freeLookup,termLabel]
  | func fn _ => exact nomatch fn

noncomputable def quoteTerms {n k : Nat} (ts : Fin k → SyntacticSemiterm language n) : Nat :=
  SemitermVec.val (fun i => (⌜ts i⌝ : Bootstrapping.Semiterm Nat language n))

theorem quoteTerms_nth {n k : Nat} (ts : Fin k → SyntacticSemiterm language n) (i : Fin k) :
    nth (quoteTerms ts) (i:Nat)=(⌜ts i⌝ : Nat) := by
  simpa [quoteTerms,FFL.FirstOrder.Semiterm.quote_def] using!
    (SemitermVec.val_nth_eq (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm Nat language n)) i)

theorem totalAtom_quote {n : Nat} (r : Relation 2)
    (ts : Fin 2 → SyntacticSemiterm language n) (b f lo z : Nat) :
    totalAtom (parameters b f lo z) 2 (Encodable.encode r) (quoteTerms ts)=
      relationalCode z (atomNamed r ts (boundLookup b) (freeLookup f)) := by
  have h0 := quoteTerms_nth ts (0:Fin 2)
  have h1 := quoteTerms_nth ts (1:Fin 2)
  simp only [Fin.val_zero,Fin.val_one] at h0 h1
  simp only [totalAtom,parameters_bound,parameters_free,parameters_reserve,h0,h1,totalLabel_quote]
  cases r <;> simp [totalHead,atomNamed,relationalCode,neighborhood_exact,membership_exact]

/-- The changing bound lookup is exactly the existing de Bruijn allocator. -/
theorem boundLookup_adjoin {n : Nat} (b lo : Nat) :
    (boundLookup (n:=n+1) (lo ∷ b))=Fin.cases lo (boundLookup b) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [boundLookup]
  · simp [boundLookup,Fin.val_succ]

local instance relationQuote (k : Nat) : GödelQuote (Relation k) Nat :=
  gödelQuoteRel (L := language) k

theorem translate_quote_rel {n k : Nat} (r : Relation k)
    (ts : Fin k → SyntacticSemiterm language n) (b f lo z : Nat) :
    translate (parameters b f lo z) (⌜FFL.FirstOrder.Semiformula.rel r ts⌝ : Nat)=
      relationalCode z (atomNamed r ts (boundLookup b) (freeLookup f)) := by
  cases r with
  | eq =>
    change translate (parameters b f lo z) (qqRel 2 0 (quoteTerms ts)) = _
    rw [translate_rel _ _ _ _ (by simp) (by simpa only [quoteTerms,Nat.cast_ofNat] using!
      (SemitermVec.isUTermVec (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm Nat language n))))]
    exact totalAtom_quote Relation.eq ts b f lo z
  | mem =>
    change translate (parameters b f lo z) (qqRel 2 1 (quoteTerms ts)) = _
    rw [translate_rel _ _ _ _ (by simp) (by simpa only [quoteTerms,Nat.cast_ofNat] using!
      (SemitermVec.isUTermVec (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm Nat language n))))]
    exact totalAtom_quote Relation.mem ts b f lo z

theorem translationNeg_standard (a : Nat) : eval translationNeg a 0 0 0=wn a := by
  rw [eval_standard]
  unfold translationNeg wn wim
  rfl

theorem translationAnd_standard (a b : Nat) :
    eval translationAnd a b 0 0=wn (wim a (wn b)) := by
  rw [eval_standard]
  unfold translationAnd wn wim
  rfl

theorem translationOr_standard (a b : Nat) :
    eval translationOr a b 0 0=wim (wn a) b := by
  rw [eval_standard]
  unfold translationOr wn wim
  rfl

theorem translationAll_standard (lo a : Nat) : eval universalExpr lo a 0 0=wal lo a := by
  rw [eval_standard]
  unfold universalExpr wal
  rfl

theorem translationExs_standard (lo a : Nat) :
    eval translationExs lo a 0 0=wn (wal lo (wn a)) := by
  rw [eval_standard]
  unfold translationExs wn wim wal
  rfl

theorem translate_quote_nrel {n k : Nat} (r : Relation k)
    (ts : Fin k → SyntacticSemiterm language n) (b f lo z : Nat) :
    translate (parameters b f lo z) (⌜FFL.FirstOrder.Semiformula.nrel r ts⌝ : Nat)=
      wn (relationalCode z (atomNamed r ts (boundLookup b) (freeLookup f))) := by
  cases r with
  | eq =>
    change translate (parameters b f lo z) (qqNRel 2 0 (quoteTerms ts)) = _
    rw [translate_nrel _ _ _ _ (by simp) (by simpa only [quoteTerms,Nat.cast_ofNat] using!
      (SemitermVec.isUTermVec (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm Nat language n)))),
      translationNeg_standard]
    exact congrArg wn (totalAtom_quote Relation.eq ts b f lo z)
  | mem =>
    change translate (parameters b f lo z) (qqNRel 2 1 (quoteTerms ts)) = _
    rw [translate_nrel _ _ _ _ (by simp) (by simpa only [quoteTerms,Nat.cast_ofNat] using!
      (SemitermVec.isUTermVec (fun j => (⌜ts j⌝ : Bootstrapping.Semiterm Nat language n)))),
      translationNeg_standard]
    exact congrArg wn (totalAtom_quote Relation.mem ts b f lo z)

/-- Algebraic calibration under explicit finite lookup environments. Freshness
and coverage are intentionally not inferred from this equality. -/
theorem translate_quote {n : Nat} (p : Semiproposition language n) (b f lo z : Nat) :
    translate (parameters b f lo z) (⌜p⌝ : Nat)=
      relationalCode z (toNamed p (boundLookup b) (freeLookup f) lo) := by
  induction p generalizing b lo with
  | rel r ts => exact translate_quote_rel r ts b f lo z
  | nrel r ts => exact translate_quote_nrel r ts b f lo z
  | verum => exact translate_verum _
  | falsum => exact translate_falsum _
  | and p q ihp ihq =>
    change translate _ (qqAnd (⌜p⌝ : Nat) (⌜q⌝ : Nat)) = _
    rw [translate_and _ _ _
      (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula
      (FFL.FirstOrder.Semiformula.quote_isSemiformula q).isUFormula,
      ihp,ihq,translationAnd_standard]
    rfl
  | or p q ihp ihq =>
    change translate _ (qqOr (⌜p⌝ : Nat) (⌜q⌝ : Nat)) = _
    rw [translate_or _ _ _
      (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula
      (FFL.FirstOrder.Semiformula.quote_isSemiformula q).isUFormula,
      ihp,ihq,translationOr_standard]
    rfl
  | all p ih =>
    change translate _ (qqAll (⌜p⌝ : Nat)) = _
    rw [translate_all _ _ (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula]
    simp only [parameters_allocator,advance_parameters,ih,translationAll_standard,boundLookup_adjoin]
    rfl
  | exs p ih =>
    change translate _ (qqExs (⌜p⌝ : Nat)) = _
    rw [translate_exs _ _ (FFL.FirstOrder.Semiformula.quote_isSemiformula p).isUFormula]
    simp only [parameters_allocator,advance_parameters,ih,translationExs_standard,boundLookup_adjoin]
    rfl

#print axioms translate_quote_nrel
#print axioms translate_quote
#print axioms totalLabel_quote
#print axioms quoteTerms_nth
#print axioms totalAtom_quote
#print axioms boundLookup_adjoin
#print axioms translate_quote_rel
end M6.PA.RelationalSource.Numeric

