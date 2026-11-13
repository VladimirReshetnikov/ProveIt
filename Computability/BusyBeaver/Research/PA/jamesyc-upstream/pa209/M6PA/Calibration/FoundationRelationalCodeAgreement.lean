module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeCalibration
@[expose] public section

/-! Replacing explicit numeric lookups by host environments requires agreement
on the formula's actual finite support. No representation is postulated. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NativeCalculus NativeCalculus.ActualBasis

theorem termLabel_agree {n : Nat} (t : SyntacticSemiterm language n)
    (b b' : Fin n → Nat) (f f' : Nat → Nat)
    (hb : ∀ i, b i=b' i) (hf : ∀ i, t.FVar? i → f i=f' i) :
    termLabel t b f=termLabel t b' f' := by
  cases t with
  | bvar i => exact hb i
  | fvar i => exact hf i (by simp)
  | func fn _ => exact nomatch fn

theorem atomNamed_agree {n k : Nat} (r : Relation k)
    (ts : Fin k → SyntacticSemiterm language n)
    (b b' : Fin n → Nat) (f f' : Nat → Nat)
    (hb : ∀ i, b i=b' i) (hf : ∀ j i, (ts j).FVar? i → f i=f' i) :
    atomNamed r ts b f=atomNamed r ts b' f' := by
  cases r <;> simp only [atomNamed] <;>
    rw [termLabel_agree _ b b' f f' hb (hf _),termLabel_agree _ b b' f f' hb (hf _)]

theorem toNamed_agree {n : Nat} (p : Semiproposition language n)
    (b b' : Fin n → Nat) (f f' : Nat → Nat) (lo : Nat)
    (hb : ∀ i, b i=b' i) (hf : ∀ i, p.FVar? i → f i=f' i) :
    toNamed p b f lo=toNamed p b' f' lo := by
  induction p generalizing lo with
  | rel r ts =>
    exact atomNamed_agree r ts b b' f f' hb (fun j i hi => hf i (by simpa using ⟨j,hi⟩))
  | nrel r ts =>
    exact congrArg Named.neg
      (atomNamed_agree r ts b b' f f' hb (fun j i hi => hf i (by simpa using ⟨j,hi⟩)))
  | verum => rfl
  | falsum => rfl
  | and p q ihp ihq =>
    simp only [toNamed]
    rw [ihp b b' lo hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inl hi))),
      ihq b b' lo hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_and i p q).mpr (Or.inr hi)))]
  | or p q ihp ihq =>
    simp only [toNamed]
    rw [ihp b b' lo hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inl hi))),
      ihq b b' lo hb (fun i hi => hf i ((FFL.FirstOrder.Semiformula.fvar?_or i p q).mpr (Or.inr hi)))]
  | all p ih =>
    simp only [toNamed]
    congr 1
    apply ih
    · intro i
      exact Fin.cases rfl hb i
    · intro i hi
      exact hf i ((FFL.FirstOrder.Semiformula.fvar?_all i p).mpr hi)
  | exs p ih =>
    simp only [toNamed]
    congr 3
    apply ih
    · intro i
      exact Fin.cases rfl hb i
    · intro i hi
      exact hf i ((FFL.FirstOrder.Semiformula.fvar?_exs i p).mpr hi)

/-- Every needed index is explicitly in range and every stored label agrees.
Only the finite support below fvSup is required for the free environment. -/
theorem translate_quote_of_agreement {n : Nat} (p : Semiproposition language n)
    (b f lo z : Nat) (bb : Fin n → Nat) (ff : Nat → Nat)
    (hb : ∀ i : Fin n, (i:Nat)<len b ∧ nth b (i:Nat)=bb i)
    (hf : ∀ i<p.fvSup, i<len f ∧ nth f i=ff i) :
    translate (parameters b f lo z) (⌜p⌝ : Nat)=relationalCode z (toNamed p bb ff lo) := by
  rw [translate_quote]
  apply congrArg (relationalCode z)
  apply toNamed_agree
  · intro i
    exact (hb i).2
  · intro i hi
    exact (hf i (FFL.FirstOrder.Semiformula.lt_fvSup_of_fvar? hi)).2

#print axioms termLabel_agree
#print axioms atomNamed_agree
#print axioms toNamed_agree
#print axioms translate_quote_of_agreement
end M6.PA.RelationalSource.Numeric

