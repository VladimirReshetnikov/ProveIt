import BusyBeaver.ZFC.ArithmeticTemplates254
import BusyBeaver.ZFC.Enum254

/-!
Fixed one-command working-state graph for the actual Enum254.
All arithmetic inputs may be internal to an arbitrary IOpen model. Intermediate
witnesses are unbounded Sigma1 witnesses; output0 imposes no spurious bounds.

The unshifted state code is P(tw,P(ws,P(d,h))). Result0 is halting NIP;
result(state+1) is a successful command, including successful allzero state.
This is not a word executor, scheduler, proof validator, or PA endpoint.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticTemplates254
attribute [local irreducible] Code254.P
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def stateValue (t s d h : V) : V := cantor t (cantor s (cantor d h))

def stateDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out t s d h. ∃ r, !ArithmeticCantor.pairDef r d h ∧
    ∃ q, !ArithmeticCantor.pairDef q s r ∧ !ArithmeticCantor.pairDef out t q”

instance state_defined : 𝚺₁-Function₄[V] stateValue via stateDef := .mk fun e => by
  simp [stateDef, stateValue]

noncomputable def someState (t s d h : V) : V := stateValue t s d h + 1

def someStateDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out t s d h. ∃ w, !stateDef w t s d h ∧ out = w + 1”

instance someState_defined : 𝚺₁-Function₄[V] someState via someStateDef := .mk fun e => by
  simp [someStateDef, someState]

/-- AX freshness is literal label inequality; collisions return truthcode0. -/
noncomputable def gateValue (a b c : V) : V :=
  if c = a ∨ c = b then 0 else bundle a b c

def gateDef : 𝚺₀.Semisentence 4 := .mkSigma
  “out a b c. ((c = a ∨ c = b) ∧ out = 0) ∨
    (c ≠ a ∧ c ≠ b ∧ !ArithmeticTemplates254.bundleDef out a b c)”

instance gate_defined : 𝚺₀-Function₃[V] gateValue via gateDef := .mk fun e => by
  classical
  by_cases ha : e 3 = e 1
  · simp [gateDef, gateValue, ha]
  · by_cases hb : e 3 = e 2 <;> simp [gateDef, gateValue, ha, hb]

/-- Exact ten pushes: rho1..rho8, GEN of the old cache, old top. -/
noncomputable def axStackValue (a h b c u t s : V) : V :=
  cantor (rho1 a b) (cantor (rho2 a b c) (cantor (rho3 a b c)
    (cantor (rho4 a b c) (cantor (rho5 a b c) (cantor (rho6 a b)
      (cantor (rho7 a b c) (cantor (rho8 a b c u) (cantor (wal a h) (cantor t s)))))))))

def axStackDef : 𝚺₁.Semisentence 8 := .mkSigma
  “out a h b c u t s.
    ∃ f1, !rho1Def f1 a b ∧ ∃ f2, !rho2Def f2 a b c ∧
    ∃ f3, !rho3Def f3 a b c ∧ ∃ f4, !rho4Def f4 a b c ∧
    ∃ f5, !rho5Def f5 a b c ∧ ∃ f6, !rho6Def f6 a b ∧
    ∃ f7, !rho7Def f7 a b c ∧ ∃ f8, !rho8Def f8 a b c u ∧
    ∃ g, !walDef g a h ∧
    ∃ s0, !ArithmeticCantor.pairDef s0 t s ∧
    ∃ s1, !ArithmeticCantor.pairDef s1 g s0 ∧
    ∃ s2, !ArithmeticCantor.pairDef s2 f8 s1 ∧
    ∃ s3, !ArithmeticCantor.pairDef s3 f7 s2 ∧
    ∃ s4, !ArithmeticCantor.pairDef s4 f6 s3 ∧
    ∃ s5, !ArithmeticCantor.pairDef s5 f5 s4 ∧
    ∃ s6, !ArithmeticCantor.pairDef s6 f4 s5 ∧
    ∃ s7, !ArithmeticCantor.pairDef s7 f3 s6 ∧
    ∃ s8, !ArithmeticCantor.pairDef s8 f2 s7 ∧
    !ArithmeticCantor.pairDef out f1 s8”

instance axStack_defined :
    HierarchySymbol.DefinedFunction (V := V)
      (fun v : Fin 7 → V => axStackValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
      axStackDef := .mk fun e => by
  simp [axStackDef, axStackValue]

/-- Total arithmetic extension of the four literal command cases. The MP
condition is exact equality, with no proof-checker predecessor/+1 condition. -/
noncomputable def effectValue (k x y u t s d h : V) : V :=
  if k = 0 then
    if wim t (d + x) = h then someState (d + x) (cantor 0 s) (d + x) 0
    else someState 0 s (d + x) 0
  else if k = 1 then someState h (cantor t s) (d + x) h
  else if k = 2 then
    if h = 1 then 0 else someState t (second s) (d + x) (first s)
  else someState (gateValue (d + x) (h + y) (k - 3))
    (axStackValue (d + x) h (h + y) (k - 3) u t s) 0 0

def effectDef : 𝚺₁.Semisentence 9 := .mkSigma
  “out k x y u t s d h.
    (k = 0 ∧
      ((!wimDef h t (d+x) ∧ ∃ p, !ArithmeticCantor.pairDef p 0 s ∧
          !someStateDef out (d+x) p (d+x) 0) ∨
       (¬ !wimDef h t (d+x) ∧ !someStateDef out 0 s (d+x) 0))) ∨
    (k ≠ 0 ∧ k = 1 ∧ ∃ p, !ArithmeticCantor.pairDef p t s ∧
      !someStateDef out h p (d+x) h) ∨
    (k ≠ 0 ∧ k ≠ 1 ∧ k = 2 ∧
      ((h = 1 ∧ out = 0) ∨
       (h ≠ 1 ∧ ∃ q, !ArithmeticCantor.secondDef q s ∧
         ∃ p, !ArithmeticCantor.firstDef p s ∧ !someStateDef out t q (d+x) p))) ∨
    (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ ∃ c, !subDef c k 3 ∧
      ∃ z, !gateDef z (d+x) (h+y) c ∧
      ∃ p, !axStackDef p (d+x) h (h+y) c u t s ∧
      !someStateDef out z p 0 0)”

instance effect_defined :
    HierarchySymbol.DefinedFunction (V := V)
      (fun v : Fin 8 → V => effectValue (v 0) (v 1) (v 2) (v 3)
        (v 4) (v 5) (v 6) (v 7)) effectDef := .mk fun e => by
  classical
  by_cases h0 : e 1 = 0
  · by_cases hm : wim (e 5) (e 7 + e 2) = e 8
    · simp [effectDef, effectValue, h0, hm]
    · have hm' := Ne.symm hm
      simp [effectDef, effectValue, h0, hm, hm']
  · by_cases h1 : e 1 = 1
    · simp [effectDef, effectValue, h1]
    · by_cases h2 : e 1 = 2
      · by_cases hh : e 8 = 1 <;> simp [effectDef, effectValue, h2, hh]
      · simp [effectDef, effectValue, h0, h1, h2]

/-- Execute the decoded raw command on the coded working state. Arguments
not used by short commands are harmless extra projections, not validity gates. -/
noncomputable def stepValue (raw w : V) : V :=
  effectValue (first raw) (first (second raw)) (first (second (second raw)))
    (first (second (second (second raw))))
    (first w) (first (second w)) (first (second (second w)))
    (second (second (second w)))

def stepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out raw w.
    ∃ k, !ArithmeticCantor.firstDef k raw ∧
    ∃ p, !ArithmeticCantor.secondDef p raw ∧
    ∃ x, !ArithmeticCantor.firstDef x p ∧
    ∃ q, !ArithmeticCantor.secondDef q p ∧
    ∃ y, !ArithmeticCantor.firstDef y q ∧
    ∃ r, !ArithmeticCantor.secondDef r q ∧
    ∃ u, !ArithmeticCantor.firstDef u r ∧
    ∃ t, !ArithmeticCantor.firstDef t w ∧
    ∃ sw, !ArithmeticCantor.secondDef sw w ∧
    ∃ s, !ArithmeticCantor.firstDef s sw ∧
    ∃ dh, !ArithmeticCantor.secondDef dh sw ∧
    ∃ d, !ArithmeticCantor.firstDef d dh ∧
    ∃ h, !ArithmeticCantor.secondDef h dh ∧
    !effectDef out k x y u t s d h”

instance step_defined : 𝚺₁-Function₂[V] stepValue via stepDef := .mk fun e => by
  simp [stepDef, stepValue]

/-- Projection-normalized exact equations for all internal raw commands. -/
theorem stepValue_mp (x rest t s d h : V) :
    stepValue (cantor 0 (cantor x rest)) (stateValue t s d h) =
      if wim t (d+x) = h then someState (d+x) (cantor 0 s) (d+x) 0
      else someState 0 s (d+x) 0 := by
  simp [stepValue, effectValue, stateValue]

theorem stepValue_drop (x rest t s d h : V) :
    stepValue (cantor 1 (cantor x rest)) (stateValue t s d h) =
      someState h (cantor t s) (d+x) h := by
  simp [stepValue, effectValue, stateValue]

theorem stepValue_nip (x rest t s d h : V) :
    stepValue (cantor 2 (cantor x rest)) (stateValue t s d h) =
      if h = 1 then 0 else someState t (second s) (d+x) (first s) := by
  simp [stepValue, effectValue, stateValue]

/-- The surplus outer tag decodes to c by actual arithmetic subtraction. -/
theorem stepValue_ax (c x y u rest t s d h : V) :
    stepValue (cantor (c+3) (cantor x (cantor y (cantor u rest))))
      (stateValue t s d h) =
    someState (gateValue (d+x) (h+y) c)
      (axStackValue (d+x) h (h+y) c u t s) 0 0 := by
  have h0 : c + 3 ≠ (0 : V) := by simp
  have h1 : c + 3 ≠ (1 : V) := by
    intro hc
    have hle : (3 : V) ≤ c + 3 := le_add_self
    simp [hc] at hle
  have h2 : c + 3 ≠ (2 : V) := by
    intro hc
    have hle : (3 : V) ≤ c + 3 := le_add_self
    rw [hc] at hle
    have hlt : (2 : V) < 2 + 1 := lt_succ_iff_le.mpr le_rfl
    rw [two_add_one_eq_three] at hlt
    exact (not_le_of_gt hlt) hle
  simp [stepValue, effectValue, stateValue, h0, h1, h2]

/-- In every internal model, the sole zero-result case is NIP with cache1.
In particular a failed MP does not become a halting result. -/
theorem effectValue_eq_zero_iff (k x y u t s d h : V) :
    effectValue k x y u t s d h = 0 ↔ k = 2 ∧ h = 1 := by
  classical
  by_cases h0 : k = 0
  · by_cases hm : wim t (d+x) = h <;> simp [effectValue, h0, hm, someState]
  · by_cases h1 : k = 1
    · simp [effectValue, h1, someState]
    · by_cases h2 : k = 2
      · by_cases hh : h = 1 <;> simp [effectValue, h2, hh, someState]
      · simp [effectValue, h0, h1, h2, someState]

theorem stepValue_eq_zero_iff (raw w : V) :
    stepValue raw w = 0 ↔ first raw = 2 ∧ second (second (second w)) = 1 := by
  exact effectValue_eq_zero_iff _ _ _ _ _ _ _ _

/-- This coding is only the working-state adapter, not the scheduler state. -/
noncomputable def encodeW (w : Enum254.W) : Nat :=
  Code254.P w.tw (Code254.P w.ws (Code254.P w.d w.h))

noncomputable def encodeResult : Option Enum254.W → Nat
  | none => 0
  | some w => encodeW w + 1

@[simp] theorem stateValue_nat (t s d h : Nat) :
    stateValue t s d h = encodeW ⟨t,s,d,h⟩ := by
  simp only [stateValue, cantor_nat, encodeW]

@[simp] theorem someState_nat (t s d h : Nat) :
    someState t s d h = encodeResult (some ⟨t,s,d,h⟩) := by
  simp only [someState, stateValue_nat, encodeResult]

@[simp] theorem gateValue_nat (a b c : Nat) : gateValue a b c = Enum254.gate a b c := by
  simp only [gateValue, bundle_nat, Enum254.gate]

@[simp] theorem axStackValue_nat (a h b c u t s : Nat) :
    axStackValue a h b c u t s = Enum254.axStack a h b c u t s := by
  simp only [axStackValue, rho1_nat, rho2_nat, rho3_nat, rho4_nat, rho5_nat,
    rho6_nat, rho7_nat, rho8_nat, wal_nat, cantor_nat, Enum254.axStack]

/-- Exact all-Nat agreement on every command and arbitrary rest pointer.
There is deliberately no accepted-proof/typed-formula premise. -/
theorem stepValue_pack_nat (cmd : Enum254.Cmd) (rest : Nat) (w : Enum254.W) :
    stepValue (Enum254.pack cmd rest) (encodeW w) =
      encodeResult (Enum254.cstep cmd w) := by
  rcases w with ⟨t,s,d,h⟩
  cases cmd with
  | mp x =>
    rw [Enum254.pack, ← cantor_nat, ← cantor_nat, ← stateValue_nat, stepValue_mp]
    by_cases he : Code254.wim t (d+x) = h <;>
      simp [wim_nat, he, Enum254.cstep, encodeResult, someState, stateValue_nat]
  | drop x =>
    rw [Enum254.pack, ← cantor_nat, ← cantor_nat, ← stateValue_nat, stepValue_drop]
    simp only [cantor_nat, someState_nat, Enum254.cstep]
  | nip x =>
    have hn := stepValue_nip (V := Nat) x rest t s d h
    simp only [← numeral_two_eq_two (M := Nat), Nat.numeral_eq] at hn
    rw [Enum254.pack, ← cantor_nat, ← cantor_nat, ← stateValue_nat, hn]
    by_cases he : h = 1 <;>
      simp [he, first_nat, second_nat, Enum254.cstep, encodeResult,
        someState, stateValue_nat, Enum254.unP]
  | ax c x y u =>
    have ha := stepValue_ax (V := Nat) c x y u rest t s d h
    simp only [← numeral_three_eq_three (M := Nat), Nat.numeral_eq] at ha
    rw [Enum254.pack, ← cantor_nat, ← cantor_nat, ← cantor_nat, ← cantor_nat,
      ← stateValue_nat, ha]
    simp only [someState_nat, gateValue_nat, axStackValue_nat, Enum254.cstep]

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandStep254
