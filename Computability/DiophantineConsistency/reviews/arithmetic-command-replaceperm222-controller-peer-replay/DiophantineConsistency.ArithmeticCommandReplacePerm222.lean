import DiophantineConsistency.ArithmeticCommandStepPerm222

/-! Actual permuted C222 raw-command tail replacement. The two short tags
have no argument, MP/tag2 retains one, and AX retains y then x. The fixed
Sigma1 graph leaves reconstruction witnesses unbounded. This is a word-code
and one-command-effect lemma, not an append/execution or compiler contract. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandReplacePerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222 ArithmeticCommandStepPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def replaceValue (raw rest : V) : V :=
  if first raw<2 then cantor (first raw) rest
  else if first raw=2 then cantor (first raw) (cantor (first (second raw)) rest)
  else cantor (first raw) (cantor (first (second raw))
    (cantor (first (second (second raw))) rest))

def replaceDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out raw rest. ∃ k, !ArithmeticCantor.firstDef k raw ∧
    ∃ payload, !ArithmeticCantor.secondDef payload raw ∧
    ((k < 2 ∧ !ArithmeticCantor.pairDef out k rest) ∨
     (¬ k < 2 ∧ ∃ p, !ArithmeticCantor.firstDef p payload ∧
       ((k = 2 ∧ ∃ v, !ArithmeticCantor.pairDef v p rest ∧
          !ArithmeticCantor.pairDef out k v) ∨
        (k ≠ 2 ∧ ∃ remaining, !ArithmeticCantor.secondDef remaining payload ∧
          ∃ q, !ArithmeticCantor.firstDef q remaining ∧
          ∃ v, !ArithmeticCantor.pairDef v q rest ∧
          ∃ w, !ArithmeticCantor.pairDef w p v ∧ !ArithmeticCantor.pairDef out k w))))”

instance replace_defined : 𝚺₁-Function₂[V] replaceValue via replaceDef := .mk fun e => by
  classical
  by_cases hs : first (e 1)<2
  · simp [replaceDef,replaceValue,hs]
  · by_cases hm : first (e 1)=2
    · simp [replaceDef,replaceValue,hm]
    · have hge : (2 : V)≤first (e 1) := le_of_not_gt hs
      simp [replaceDef,replaceValue,hs,hm,hge]
instance replace_definable : 𝚺₁-Function₂[V] replaceValue := replace_defined.to_definable

theorem replace_total (raw rest : V) : ∃! out,replaceDef.val.Evalb ![out,raw,rest] := by simp

@[simp] theorem replace_nip (r rest : V) : replaceValue (cantor 0 r) rest=cantor 0 rest := by
  simp [replaceValue]
@[simp] theorem replace_drop (r rest : V) : replaceValue (cantor 1 r) rest=cantor 1 rest := by
  simp [replaceValue]
@[simp] theorem replace_mp (x r rest : V) :
    replaceValue (cantor 2 (cantor x r)) rest=cantor 2 (cantor x rest) := by
  simp [replaceValue]
@[simp] theorem replace_ax (c y x r rest : V) :
    replaceValue (cantor (c+3) (cantor y (cantor x r))) rest=
      cantor (c+3) (cantor y (cantor x rest)) := by
  have h23 : (2 : V)<3 := by simpa only [two_add_one_eq_three] using lt_add_one (2 : V)
  have h2 : (2 : V)<c+3 := lt_of_lt_of_le h23 le_add_self
  simp [replaceValue,not_lt_of_ge (le_of_lt h2),ne_of_gt h2]

@[simp] theorem first_replace (raw rest : V) : first (replaceValue raw rest)=first raw := by
  by_cases hs : first raw<2
  · simp [replaceValue,hs]
  · by_cases hm : first raw=2 <;> simp [replaceValue,hs,hm]

@[simp] theorem tail_replace (raw rest : V) : tailValue (replaceValue raw rest)=rest := by
  by_cases hs : first raw<2
  · simp [replaceValue,tailValue,hs]
  · by_cases hm : first raw=2 <;> simp [replaceValue,tailValue,hs,hm]

@[simp] theorem replace_twice (raw left right : V) :
    replaceValue (replaceValue raw left) right=replaceValue raw right := by
  by_cases hs : first raw<2
  · simp [replaceValue,hs]
  · by_cases hm : first raw=2 <;> simp [replaceValue,hs,hm]

@[simp] theorem replace_own_tail (raw : V) : replaceValue raw (tailValue raw)=raw := by
  by_cases hs : first raw<2
  · simp [replaceValue,tailValue,hs]
  · by_cases hm : first raw=2
    · simpa [replaceValue,tailValue,hs,hm] using (cantor_projections raw)
    · simp [replaceValue,tailValue,hs,hm]

/-- Unused projections may change on short commands; the actual effect ignores
those projections. Both meaningful AX arguments and old counter are retained. -/
theorem step_replace (raw rest w : V) :
    stepValue (replaceValue raw rest) w=stepValue raw w := by
  by_cases hs : first raw<2
  · rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hs) with h0 | h1
    · simp [stepValue,replaceValue,effectValue,h0]
    · simp [stepValue,replaceValue,effectValue,h1]
  · by_cases hm : first raw=2
    · simp [stepValue,replaceValue,effectValue,hm]
    · simp [stepValue,replaceValue,hs,hm]

/-- Every actual command and arbitrary tail, including raw0/NIP. -/
theorem replace_pack_nat (cmd : EnumPerm.Cmd) (r rest : ℕ) :
    replaceValue (EnumPerm.pack cmd r) rest=EnumPerm.pack cmd rest := by
  cases cmd with
  | nip => simpa only [EnumPerm.pack,←cantor_nat] using replace_nip r rest
  | drop => simpa only [EnumPerm.pack,←cantor_nat] using replace_drop r rest
  | mp x =>
    have h := replace_mp (V := ℕ) x r rest
    simp only [←numeral_two_eq_two (M := ℕ),Nat.numeral_eq] at h
    simpa only [EnumPerm.pack,←cantor_nat] using h
  | ax c x y =>
    have h := replace_ax (V := ℕ) c y x r rest
    simp only [←numeral_three_eq_three (M := ℕ),Nat.numeral_eq] at h
    simpa only [EnumPerm.pack,←cantor_nat] using h

theorem replace_nat (raw rest : ℕ) :
    replaceValue raw rest=EnumPerm.pack (EnumPerm.decode raw).1 rest := by
  have h := replace_pack_nat (EnumPerm.decode raw).1 (EnumPerm.decode raw).2 rest
  simpa only [pack_decode] using h

end DiophantineConsistency.ArithmeticCommandReplacePerm222
