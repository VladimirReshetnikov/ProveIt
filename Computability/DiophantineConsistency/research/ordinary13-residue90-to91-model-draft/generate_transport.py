#!/usr/bin/env python3
"""Reconstruct the inert 90/91 gamma-valuation transport; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent
s='''import Residue91Residuals
import Residue90XZeroGraph
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.IPRAExpressionNative
import Mathlib.Tactic.Ring

/-! Proposed 90/91 gamma transport; no Lean elaboration or endpoint replay. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.Residue90To91TransportDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open Residue90CompactPortBoundsDraft

def raiseGamma {V : Type*} [Add V] [One V] (v : Fin 13 → V) (i : Fin 13) : V :=
  if i=12 then v i+1 else v i

def lowerGamma {V : Type*} [Sub V] [One V] (v : Fin 13 → V) (i : Fin 13) : V :=
  if i=12 then v i-1 else v i

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem raise_lower (v : Fin 13 → V) (h : 0<v 12) : raiseGamma (lowerGamma v)=v := by
  funext i
  fin_cases i <;> simp [raiseGamma,lowerGamma,tsub_add_cancel_of_le (pos_iff_one_le.mp h)]

'''
for i in range(4):
 s+=f'''theorem relation{i:02d} (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    (Residue91ResidualsDraft.residuals p {i}).evalRing (fun k => ι (v k)) =
      (Residue90ResidualsDraft.residuals p {i}).evalRing (fun k => ι (raiseGamma v k)) := by
  simp [Residue91ResidualsDraft.residuals, Residue90ResidualsDraft.residuals,
    raiseGamma,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    map_add,map_mul,map_one] <;> ring

'''
s+='''theorem evaluation (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    (Residue91LiteralDraft.literal p).evalRing (fun k => ι (v k)) =
      (Residue90LiteralDraft.literal p).evalRing (fun k => ι (raiseGamma v k)) := by
  rw [←Residue91ResidualsDraft.sum_eq_literal,←Residue90ResidualsDraft.sum_eq_literal]
  simp only [Residue91ResidualsDraft.sum,Residue90ResidualsDraft.sum,
    Expr.evalRing_add,Expr.evalRing_mul,relation00 p v,relation01 p v,relation02 p v,relation03 p v]

theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (Residue91LiteralDraft.literal p) v ↔
      InternalZero (Residue90LiteralDraft.literal p) (raiseGamma v) := by
  rw [ModelDifferenceRing.internalZero_iff,ModelDifferenceRing.internalZero_iff,evaluation p v]

theorem compact_no_zero_iff (K : ℕ) :
    (∀ v : Fin 13 → V, ¬InternalZero (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) v) ↔
      ∀ v : Fin 13 → V, ¬InternalZero (Residue91LiteralDraft.literal (fun j => (ports K j:ℤ))) v := by
  constructor
  · intro h v hz
    exact h (raiseGamma v) ((zero_iff _ v).mp hz)
  · intro h v hz
    have hg := Residue90XZeroGraphDraft.compact_gamma_positive K v hz
    have hlift := raise_lower v hg
    apply h (lowerGamma v)
    apply (zero_iff _ (lowerGamma v)).mpr
    simpa only [hlift] using hz

theorem compact_sameNoZero (K : ℕ) : SameNoZero
    (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ)))
    (Residue91LiteralDraft.literal (fun j => (ports K j:ℤ))) := by
  intro V _ _
  exact compact_no_zero_iff (V:=V) K

/-- Parent bridge is an explicit external Lean hypothesis; no fixed-kernel
endpoint or physical coefficient binding is supplied. -/
theorem polynomialBridge (K : ℕ)
    (hparent : PolynomialBridge (Residue91LiteralDraft.literal (fun j => (ports K j:ℤ)))) :
    PolynomialBridge (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) :=
  HAExpressionNoZeroEquiv.bridge _ _ (compact_sameNoZero K) hparent

theorem native_equivalence (K : ℕ)
    (hparent : PolynomialBridge (Residue91LiteralDraft.literal (fun j => (ports K j:ℤ)))) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (polynomialBridge K hparent)
end DiophantineConsistency.Residue90To91TransportDraft
#print axioms DiophantineConsistency.Residue90To91TransportDraft.compact_no_zero_iff
#print axioms DiophantineConsistency.Residue90To91TransportDraft.native_equivalence
'''
t=P/'Residue90To91Transport.lean.src'
if '--initialize' in sys.argv:t.write_text(s)
else:assert t.read_text()==s
print(json.dumps({'scope':'source transport reconstruction, no Lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'residual_relations':4},sort_keys=True,indent=2))
