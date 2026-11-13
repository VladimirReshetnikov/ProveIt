import DiophantineConsistency.ArithmeticCommandWordPerm222
import BusyBeaver.ZFC.ArithmeticSeedTemplates222

/-! # One represented command of the actual permuted C222 enumerator

The fixed graphs work over arbitrary internal IOpen inputs, hence also IΣ1
inputs. Zero is the halting result; a successful working state is coded plus
one. The unshifted working-state code is P(tw,P(ws,P(d,h))). The two short
commands read no argument and preserve d. MP reads one argument. AX reads
y then x, uses the old d as its dominated fourth argument and GEN label,
and pushes the actual growG and helper-free C222 seed.

This is one-command arithmetic, not a scheduler, bounded-run invariant,
represented proof soundness theorem, or PA/HA consistency equivalence.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace DiophantineConsistency.ArithmeticCommandStepPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254 ArithmeticTemplates254
attribute [local irreducible] Code254.P

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def stateValue (t s d h : V) : V := cantor t (cantor s (cantor d h))

def stateDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out t s d h. ∃ r, !ArithmeticCantor.pairDef r d h ∧
    ∃ q, !ArithmeticCantor.pairDef q s r ∧ !ArithmeticCantor.pairDef out t q”

instance state_defined : 𝚺₁-Function₄[V] stateValue via stateDef :=
  .mk fun e => by simp [stateDef, stateValue]

noncomputable def someState (t s d h : V) : V := stateValue t s d h + 1

def someStateDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out t s d h. ∃ w, !stateDef w t s d h ∧ out = w + 1”

instance someState_defined : 𝚺₁-Function₄[V] someState via someStateDef :=
  .mk fun e => by simp [someStateDef, someState]

/-- Numeric label collisions yield truth, not a failed or halting command. -/
noncomputable def gateValue (a b c : V) : V :=
  if c = a ∨ c = b then 0 else ArithmeticSeedTemplates222.bundle222 a b c

def gateDef : 𝚺₀.Semisentence 4 := .mkSigma
  “out a b c. ((c = a ∨ c = b) ∧ out = 0) ∨
    (c ≠ a ∧ c ≠ b ∧ !ArithmeticSeedTemplates222.bundleDef out a b c)”

instance gate_defined : 𝚺₀-Function₃[V] gateValue via gateDef := .mk fun e => by
  classical
  by_cases ha : e 3 = e 1
  · simp [gateDef, gateValue, ha]
  · by_cases hb : e 3 = e 2 <;> simp [gateDef, gateValue, ha, hb]

/-- Head first: rho1..rho5, rho6(a,c), growG, rho8, GEN at u, old top.
The actual AX effect below always supplies u=d, rather than a fourth payload. -/
noncomputable def axStackValue (a h b c u t s : V) : V :=
  cantor (rho1 a b) (cantor (rho2 a b c) (cantor (rho3 a b c)
    (cantor (rho4 a b c) (cantor (rho5 a b c) (cantor (rho6 a c)
      (cantor (ArithmeticTemplates222.growG a b c) (cantor (rho8 a b c u)
        (cantor (wal u h) (cantor t s)))))))))

def axStackDef : 𝚺₁.Semisentence 8 := .mkSigma
  “out a h b c u t s.
    ∃ f1, !rho1Def f1 a b ∧ ∃ f2, !rho2Def f2 a b c ∧
    ∃ f3, !rho3Def f3 a b c ∧ ∃ f4, !rho4Def f4 a b c ∧
    ∃ f5, !rho5Def f5 a b c ∧ ∃ f6, !rho6Def f6 a c ∧
    ∃ fG, !ArithmeticTemplates222.growGDef fG a b c ∧
    ∃ f8, !rho8Def f8 a b c u ∧ ∃ g, !walDef g u h ∧
    ∃ s0, !ArithmeticCantor.pairDef s0 t s ∧
    ∃ s1, !ArithmeticCantor.pairDef s1 g s0 ∧
    ∃ s2, !ArithmeticCantor.pairDef s2 f8 s1 ∧
    ∃ s3, !ArithmeticCantor.pairDef s3 fG s2 ∧
    ∃ s4, !ArithmeticCantor.pairDef s4 f6 s3 ∧
    ∃ s5, !ArithmeticCantor.pairDef s5 f5 s4 ∧
    ∃ s6, !ArithmeticCantor.pairDef s6 f4 s5 ∧
    ∃ s7, !ArithmeticCantor.pairDef s7 f3 s6 ∧
    ∃ s8, !ArithmeticCantor.pairDef s8 f2 s7 ∧
    !ArithmeticCantor.pairDef out f1 s8”

instance axStack_defined : HierarchySymbol.DefinedFunction (V := V)
    (fun v : Fin 7 → V => axStackValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    axStackDef := .mk fun e => by simp [axStackDef, axStackValue]

/-- p and q are the first and second payload fields. Thus MP uses p=x,
whereas AX uses p=y,q=x. Unused projections impose no validity condition. -/
noncomputable def effectValue (k p q t s d h : V) : V :=
  if k = 0 then
    if h = 1 then 0 else someState t (second s) d (first s)
  else if k = 1 then someState h (cantor t s) d h
  else if k = 2 then
    if wim t (d+p) = h then someState (d+p) (cantor 0 s) (d+p) 0
    else someState 0 s (d+p) 0
  else someState (gateValue (d+q) (h+p) (k-3))
    (axStackValue (d+q) h (h+p) (k-3) d t s) 0 0

def effectDef : 𝚺₁.Semisentence 8 := .mkSigma
  “out k p q t s d h.
    (k = 0 ∧ ((h = 1 ∧ out = 0) ∨
      (h ≠ 1 ∧ ∃ v, !ArithmeticCantor.secondDef v s ∧
        ∃ u, !ArithmeticCantor.firstDef u s ∧ !someStateDef out t v d u))) ∨
    (k ≠ 0 ∧ k = 1 ∧ ∃ v, !ArithmeticCantor.pairDef v t s ∧
      !someStateDef out h v d h) ∨
    (k ≠ 0 ∧ k ≠ 1 ∧ k = 2 ∧
      ((!wimDef h t (d+p) ∧ ∃ v, !ArithmeticCantor.pairDef v 0 s ∧
          !someStateDef out (d+p) v (d+p) 0) ∨
       (¬ !wimDef h t (d+p) ∧ !someStateDef out 0 s (d+p) 0))) ∨
    (k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2 ∧ ∃ c, !subDef c k 3 ∧
      ∃ z, !gateDef z (d+q) (h+p) c ∧
      ∃ v, !axStackDef v (d+q) h (h+p) c d t s ∧ !someStateDef out z v 0 0)”

instance effect_defined : HierarchySymbol.DefinedFunction (V := V)
    (fun v : Fin 7 → V => effectValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    effectDef := .mk fun e => by
  classical
  by_cases h0 : e 1 = 0
  · by_cases hh : e 7 = 1 <;> simp [effectDef, effectValue, h0, hh]
  · by_cases h1 : e 1 = 1
    · simp [effectDef, effectValue, h1]
    · by_cases h2 : e 1 = 2
      · by_cases hm : wim (e 4) (e 6 + e 2) = e 7
        · simp [effectDef, effectValue, h2, hm]
        · have hm' := Ne.symm hm
          simp [effectDef, effectValue, h2, hm, hm']
      · simp [effectDef, effectValue, h0, h1, h2]

noncomputable def stepValue (raw w : V) : V :=
  effectValue (first raw) (first (second raw)) (first (second (second raw)))
    (first w) (first (second w)) (first (second (second w)))
    (second (second (second w)))

def stepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out raw w.
    ∃ k, !ArithmeticCantor.firstDef k raw ∧
    ∃ rp, !ArithmeticCantor.secondDef rp raw ∧
    ∃ p, !ArithmeticCantor.firstDef p rp ∧
    ∃ rq, !ArithmeticCantor.secondDef rq rp ∧
    ∃ q, !ArithmeticCantor.firstDef q rq ∧
    ∃ t, !ArithmeticCantor.firstDef t w ∧
    ∃ sw, !ArithmeticCantor.secondDef sw w ∧
    ∃ s, !ArithmeticCantor.firstDef s sw ∧
    ∃ dh, !ArithmeticCantor.secondDef dh sw ∧
    ∃ d, !ArithmeticCantor.firstDef d dh ∧
    ∃ h, !ArithmeticCantor.secondDef h dh ∧ !effectDef out k p q t s d h”

instance step_defined : 𝚺₁-Function₂[V] stepValue via stepDef :=
  .mk fun e => by simp [stepDef, stepValue]

instance step_definable : 𝚺₁-Function₂[V] stepValue := step_defined.to_definable

theorem step_total (raw w : V) : ∃! out, stepDef.val.Evalb ![out,raw,w] := by simp

theorem stepValue_nip (rest t s d h : V) :
    stepValue (cantor 0 rest) (stateValue t s d h) =
      if h = 1 then 0 else someState t (second s) d (first s) := by
  simp [stepValue, effectValue, stateValue]

theorem stepValue_drop (rest t s d h : V) :
    stepValue (cantor 1 rest) (stateValue t s d h) =
      someState h (cantor t s) d h := by
  simp [stepValue, effectValue, stateValue]

theorem stepValue_mp (x rest t s d h : V) :
    stepValue (cantor 2 (cantor x rest)) (stateValue t s d h) =
      if wim t (d+x) = h then someState (d+x) (cantor 0 s) (d+x) 0
      else someState 0 s (d+x) 0 := by
  simp [stepValue, effectValue, stateValue]

theorem stepValue_ax (c y x rest t s d h : V) :
    stepValue (cantor (c+3) (cantor y (cantor x rest))) (stateValue t s d h) =
      someState (gateValue (d+x) (h+y) c)
        (axStackValue (d+x) h (h+y) c d t s) 0 0 := by
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

/-- Dominance is automatic for the actual old-counter fourth argument. -/
theorem ax_rho8_dominated (d x : V) : d ≤ d+x := le_self_add

theorem effectValue_eq_zero_iff (k p q t s d h : V) :
    effectValue k p q t s d h = 0 ↔ k = 0 ∧ h = 1 := by
  classical
  by_cases h0 : k = 0
  · by_cases hh : h = 1 <;> simp [effectValue, h0, hh, someState]
  · by_cases h1 : k = 1
    · simp [effectValue, h1, someState]
    · by_cases h2 : k = 2
      · by_cases hm : wim t (d+p) = h <;> simp [effectValue, h2, hm, someState]
      · simp [effectValue, h0, h1, h2, someState]

theorem stepValue_eq_zero_iff (raw w : V) :
    stepValue raw w = 0 ↔ first raw = 0 ∧ second (second (second w)) = 1 :=
  effectValue_eq_zero_iff _ _ _ _ _ _ _

/-- These adapters mention the actual EnumPerm working registers. -/
def encodeW (w : EnumPerm.W) : ℕ := Code254.P w.tw (Code254.P w.ws (Code254.P w.d w.h))

def encodeResult : Option EnumPerm.W → ℕ
  | none => 0
  | some w => encodeW w + 1

@[simp] theorem stateValue_nat (t s d h : ℕ) :
    stateValue t s d h = encodeW ⟨t,s,d,h⟩ := by
  simp only [stateValue, cantor_nat, encodeW]

@[simp] theorem someState_nat (t s d h : ℕ) :
    someState t s d h = encodeResult (some ⟨t,s,d,h⟩) := by
  simp only [someState, stateValue_nat, encodeResult]

@[simp] theorem gateValue_nat (a b c : ℕ) : gateValue a b c = EnumPerm.gate a b c := by
  simp only [gateValue, ArithmeticSeedTemplates222.bundle222_nat, EnumPerm.gate]

@[simp] theorem axStackValue_nat (a h b c u t s : ℕ) :
    axStackValue a h b c u t s = EnumPerm.axStack a h b c u t s := by
  simp only [axStackValue, rho1_nat, rho2_nat, rho3_nat, rho4_nat, rho5_nat,
    rho6_nat, ArithmeticTemplates222.growG_nat, rho8_nat, wal_nat, cantor_nat, EnumPerm.axStack]

theorem stepValue_pack_nat (cmd : EnumPerm.Cmd) (rest : ℕ) (w : EnumPerm.W) :
    stepValue (EnumPerm.pack cmd rest) (encodeW w) = encodeResult (EnumPerm.cstep cmd w) := by
  rcases w with ⟨t,s,d,h⟩
  cases cmd with
  | nip =>
    rw [EnumPerm.pack, ← cantor_nat, ← stateValue_nat, stepValue_nip]
    by_cases he : h = 1 <;>
      simp [he, first_nat, second_nat, EnumPerm.cstep, encodeResult,
        someState, stateValue_nat, EnumPerm.unP]
  | drop =>
    rw [EnumPerm.pack, ← cantor_nat, ← stateValue_nat, stepValue_drop]
    simp only [cantor_nat, someState_nat, EnumPerm.cstep]
  | mp x =>
    have hm := stepValue_mp (V := ℕ) x rest t s d h
    simp only [← numeral_two_eq_two (M := ℕ), Nat.numeral_eq] at hm
    rw [EnumPerm.pack, ← cantor_nat, ← cantor_nat, ← stateValue_nat, hm]
    by_cases he : Code254.wim t (d+x) = h <;>
      simp [wim_nat, he, EnumPerm.cstep, encodeResult, someState, stateValue_nat]
  | ax c x y =>
    have ha := stepValue_ax (V := ℕ) c y x rest t s d h
    simp only [← numeral_three_eq_three (M := ℕ), Nat.numeral_eq] at ha
    rw [EnumPerm.pack, ← cantor_nat, ← cantor_nat, ← cantor_nat, ← stateValue_nat, ha]
    simp only [someState_nat, gateValue_nat, axStackValue_nat, EnumPerm.cstep]

/-- Every raw input is exactly repacked, without a code-validity restriction. -/
theorem pack_decode (raw : ℕ) :
    EnumPerm.pack (EnumPerm.decode raw).1 (EnumPerm.decode raw).2 = raw := by
  have h0 : Code254.P (EnumPerm.unP raw).1 (EnumPerm.unP raw).2 = raw := by
    simpa only [Code254.P, EnumPerm.unP] using _root_.SetTheory.Cantor.toNat_ofNat raw
  have h1 : Code254.P (EnumPerm.unP (EnumPerm.unP raw).2).1
      (EnumPerm.unP (EnumPerm.unP raw).2).2 = (EnumPerm.unP raw).2 := by
    simpa only [Code254.P, EnumPerm.unP] using
      _root_.SetTheory.Cantor.toNat_ofNat (EnumPerm.unP raw).2
  have h2 : Code254.P (EnumPerm.unP (EnumPerm.unP (EnumPerm.unP raw).2).2).1
      (EnumPerm.unP (EnumPerm.unP (EnumPerm.unP raw).2).2).2 =
        (EnumPerm.unP (EnumPerm.unP raw).2).2 := by
    simpa only [Code254.P, EnumPerm.unP] using
      _root_.SetTheory.Cantor.toNat_ofNat (EnumPerm.unP (EnumPerm.unP raw).2).2
  rcases hk : (EnumPerm.unP raw).1 with _ | _ | _ | k <;>
    simpa only [EnumPerm.decode, hk, EnumPerm.pack, h2, h1] using h0

theorem stepValue_nat (raw : ℕ) (w : EnumPerm.W) :
    stepValue raw (encodeW w) = encodeResult (EnumPerm.cstep (EnumPerm.decode raw).1 w) := by
  have h := stepValue_pack_nat (EnumPerm.decode raw).1 (EnumPerm.decode raw).2 w
  simpa only [pack_decode] using h

end DiophantineConsistency.ArithmeticCommandStepPerm222
