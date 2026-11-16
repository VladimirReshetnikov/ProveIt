import PA194RadixRecodingEquation

set_option autoImplicit false
set_option maxRecDepth 22000
set_option maxHeartbeats 6500000
set_option linter.unusedSectionVars false

namespace PA194RadixRecoding
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion
open PA194ClockInvariantDefinable PA194MachineProjections TableDispatch PA194RadixModel
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem recodePositive (sourceLast targetLast : Nat) (n : M) (hn : 0 < n)
    (hsource : (2 : M) ≤ modelNumeral M (sourceLast+1)) :
    let source := modelNumeral M (sourceLast+1)
    let target := modelNumeral M (targetLast+1)
    let tag := n % source
    let left := F fixedFirst ![n/source]
    let right := F fixedSecond ![n/source]
    F (recode sourceLast targetLast) ![n] =
      if tag < target then
        encode target (F (recode sourceLast targetLast) ![left])
          (F (recode sourceLast targetLast) ![right]) tag
      else 0 := by
  rcases zero_or_succ n with hz | ⟨pred,rfl⟩
  · exact False.elim (_root_.lt_irrefl _ (hz ▸ hn))
  · exact recodeSucc sourceLast targetLast pred hsource

private theorem encodeZero (radix : M) : encode radix 0 0 0 = 0 := by
  simp [encode,cantor,triangle]

/-- Recoding preserves every constructor whose digit is available in both
    radices. In particular it preserves the variable identifiers built into
    the two components of a binder or an atom. -/
theorem recodeConstructor (sourceLast targetLast : Nat) (left right tag : M)
    (hsource : (2 : M) ≤ modelNumeral M (sourceLast+1))
    (hte : tag < modelNumeral M (sourceLast+1))
    (ht : tag < modelNumeral M (targetLast+1)) :
    F (recode sourceLast targetLast) ![encode (modelNumeral M (sourceLast+1)) left right tag] =
      encode (modelNumeral M (targetLast+1))
        (F (recode sourceLast targetLast) ![left]) (F (recode sourceLast targetLast) ![right]) tag := by
  let source := modelNumeral M (sourceLast+1)
  let target := modelNumeral M (targetLast+1)
  let number := encode source left right tag
  change F (recode sourceLast targetLast) ![number] =
    encode target (F (recode sourceLast targetLast) ![left]) (F (recode sourceLast targetLast) ![right]) tag
  by_cases hzero : number = 0
  · have hspos : (0 : M) < source := lt_of_le_of_lt zero_le hte
    have h := constructorInj source left right tag 0 0 0 hte hspos (hzero.trans (encodeZero source).symm)
    obtain ⟨hleft,hright,htag⟩ := h
    rw [hzero,hleft,hright,htag,recodeZero,encodeZero]
  · have hpos : (0 : M) < number := lt_of_le_of_ne zero_le (Ne.symm hzero)
    obtain ⟨hleft,hright,htag⟩ := decoded source left right tag hte
    rw [recodePositive sourceLast targetLast number hpos hsource,htag,hleft,hright,if_pos ht]

theorem recodeDigit (sourceLast targetLast : Nat) (tag : M)
    (hsource : (2 : M) ≤ modelNumeral M (sourceLast+1))
    (hte : tag < modelNumeral M (sourceLast+1))
    (ht : tag < modelNumeral M (targetLast+1)) :
    F (recode sourceLast targetLast) ![tag] = tag := by
  have htag (radix : M) : encode radix 0 0 tag = tag := by
    simp [encode,cantor,triangle]
  simpa only [htag,recodeZero] using recodeConstructor sourceLast targetLast 0 0 tag hsource hte ht

private theorem strongForSigma1 (property : M → Prop) (hdef : 𝚺₁-Predicate property)
    (step : ∀ x : M, (∀ u : M, u < x → property u) → property x) :
    ∀ x : M, property x := by
  haveI := hdef
  have bounded : 𝚺₁-Predicate (fun x : M => ∀ u < x, property u) := by definability
  have proof : ∀ x : M, ∀ u < x, property u := by
    intro x
    induction x using ISigma1.sigma1_succ_induction with
    | hP => exact bounded
    | zero => exact fun u hu => False.elim (not_lt_zero hu)
    | succ x ih =>
      intro u hu
      rcases lt_or_eq_of_le (lt_succ_iff_le.mp hu) with h | he
      · exact ih u h
      · rw [he]
        exact step x ih
  exact fun x => step x (proof x)

private theorem compositionEqDef (forward back : M → M) (hf : 𝚺₁-Function₁ forward)
    (hb : 𝚺₁-Function₁ back) : 𝚺₁-Predicate (fun x : M => back (forward x) = x) := by
  haveI := hf
  haveI := hb
  definability

/-- Decoding back is a left inverse on the entire source radix. The target
    radix may have additional digits that the backward code maps to zero. -/
theorem roundTrip (sourceLast targetLast : Nat) (n : M)
    (hsource : (2 : M) ≤ modelNumeral M (sourceLast+1))
    (horder : modelNumeral M (sourceLast+1) ≤ modelNumeral M (targetLast+1)) :
    F (recode targetLast sourceLast) ![F (recode sourceLast targetLast) ![n]] = n := by
  let source := modelNumeral M (sourceLast+1)
  let target := modelNumeral M (targetLast+1)
  let forward : M → M := fun x => F (recode sourceLast targetLast) ![x]
  let back : M → M := fun x => F (recode targetLast sourceLast) ![x]
  have hforward : 𝚺₁-Function₁ forward := unaryCodeDef _
  have hback : 𝚺₁-Function₁ back := unaryCodeDef _
  change back (forward n) = n
  apply strongForSigma1 (fun x => back (forward x) = x) (compositionEqDef forward back hforward hback) _ n
  intro x ih
  by_cases hx : x = 0
  · subst x
    change F (recode targetLast sourceLast) ![F (recode sourceLast targetLast) ![(0 : M)]] = 0
    rw [recodeZero,recodeZero]
  · have hxpos : (0 : M) < x := lt_of_le_of_ne zero_le (Ne.symm hx)
    let left := F fixedFirst ![x/source]
    let right := F fixedSecond ![x/source]
    let tag := x%source
    have hparts : encode source left right tag = x := reconstruct source x
    have hbds : left < x ∧ right < x := decoderDescent source x hsource hxpos
    have hspos : (0 : M) < source := lt_of_lt_of_le (by norm_num) hsource
    have htag : tag < source := mod_lt x hspos
    have htag' : tag < target := lt_of_lt_of_le htag horder
    have htarget : (2 : M) ≤ target := le_trans hsource horder
    have hForward : forward x = encode target (forward left) (forward right) tag := by
      rw [←hparts]
      exact recodeConstructor sourceLast targetLast left right tag hsource htag htag'
    calc
      back (forward x) = back (encode target (forward left) (forward right) tag) :=
        congrArg back hForward
      _ = encode source (back (forward left)) (back (forward right)) tag :=
        recodeConstructor targetLast sourceLast (forward left) (forward right) tag htarget htag' htag
      _ = x := by rw [ih left hbds.1,ih right hbds.2,hparts]

theorem injective (sourceLast targetLast : Nat)
    (hsource : (2 : M) ≤ modelNumeral M (sourceLast+1))
    (horder : modelNumeral M (sourceLast+1) ≤ modelNumeral M (targetLast+1)) :
    Function.Injective (fun x : M => F (recode sourceLast targetLast) ![x]) := by
  intro a b h
  have same := congrArg (fun x : M => F (recode targetLast sourceLast) ![x]) h
  rw [roundTrip sourceLast targetLast a hsource horder,
    roundTrip sourceLast targetLast b hsource horder] at same
  exact same

/-- Recode from radix four to five, then back to four. -/
theorem radixFiveRoundTrip (n : M) :
    F (recode 4 3) ![F (recode 3 4) ![n]] = n := by
  apply roundTrip 3 4 n
  · have htwo : modelNumeral M 2 = (2 : M) := by
      rw [show (2 : Nat) = 1+1 from rfl,PA194FiniteControls.modelNumeralSucc,
        PA194StateOne.modelNumeralOne]
      norm_num
    rw [←htwo]
    exact le_of_lt (PA194StateOne.modelNumeralStrict 2 4 (by decide))
  · exact le_of_lt (PA194StateOne.modelNumeralStrict 4 5 (by decide))

#print axioms recodeConstructor
#print axioms recodeDigit
#print axioms roundTrip
#print axioms injective
#print axioms radixFiveRoundTrip
end models
end PA194RadixRecoding
