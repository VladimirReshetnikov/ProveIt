#!/usr/bin/env python3
"""Reconstruct inert first-root shift transport; no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent
s='''import ResidueFoldP89Residuals
import Residue90To82Transport
import Mathlib.Tactic.Ring

/-! Conditional 89/90 first-root transport. Forced-r is an explicit
hypothesis; all sources and imported providers remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.Residue89To90TransportDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing HAExpressionAssembly HAExpressionNoZeroEquiv
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open Residue90CompactPortBoundsDraft

def raiseR {V : Type*} [Add V] [One V] (v : Fin 13 → V) (i : Fin 13) : V :=
  if i=8 then v i+1 else v i

def lowerR {V : Type*} [Sub V] [One V] (v : Fin 13 → V) (i : Fin 13) : V :=
  if i=8 then v i-1 else v i

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem raise_lower (v : Fin 13 → V) (h : 0<v 8) : raiseR (lowerR v)=v := by
  funext i
  fin_cases i <;> simp [raiseR,lowerR,tsub_add_cancel_of_le (pos_iff_one_le.mp h)]

'''
for i in range(4):
 s+=f'''theorem relation{i:02d} (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    (Residue90ResidualsDraft.residuals p {i}).evalRing (fun k => ι (v k)) =
      (ResidueFoldP89DraftResiduals.residuals p {i}).evalRing (fun k => ι (raiseR v k)) := by
  simp [Residue90ResidualsDraft.residuals,ResidueFoldP89DraftResiduals.residuals,
    raiseR,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    map_add,map_mul,map_one] <;> ring

'''
s+='''theorem evaluation (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    (Residue90LiteralDraft.literal p).evalRing (fun k => ι (v k)) =
      (ResidueFoldP89Draft.literal p).evalRing (fun k => ι (raiseR v k)) := by
  rw [←Residue90ResidualsDraft.sum_eq_literal,←ResidueFoldP89DraftResiduals.sum_eq_literal]
  simp only [Residue90ResidualsDraft.sum,ResidueFoldP89DraftResiduals.sum,
    Expr.evalRing_add,Expr.evalRing_mul,relation00 p v,relation01 p v,relation02 p v,relation03 p v]

theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (Residue90LiteralDraft.literal p) v ↔
      InternalZero (ResidueFoldP89Draft.literal p) (raiseR v) := by
  rw [ModelDifferenceRing.internalZero_iff,ModelDifferenceRing.internalZero_iff,evaluation p v]

/-- The graph forcing and model K bound needed to prove it are deliberately
not silently supplied by the finite checker. -/
def ForcedR (K : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (v : Fin 13 → V),
    InternalZero (ResidueFoldP89Draft.literal (fun j => (ports K j:ℤ))) v → 0<v 8

theorem compact_no_zero_iff (K : ℕ)
    (hr : ∀ v : Fin 13 → V,
      InternalZero (ResidueFoldP89Draft.literal (fun j => (ports K j:ℤ))) v → 0<v 8) :
    (∀ v : Fin 13 → V, ¬InternalZero (ResidueFoldP89Draft.literal (fun j => (ports K j:ℤ))) v) ↔
      ∀ v : Fin 13 → V, ¬InternalZero (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) v := by
  constructor
  · intro h v hz
    exact h (raiseR v) ((zero_iff _ v).mp hz)
  · intro h v hz
    have hp := hr v hz
    have hlift := raise_lower v hp
    apply h (lowerR v)
    apply (zero_iff _ (lowerR v)).mpr
    simpa only [hlift] using hz

theorem compact_sameNoZero (K : ℕ) (hr : ForcedR K) : SameNoZero
    (ResidueFoldP89Draft.literal (fun j => (ports K j:ℤ)))
    (Residue90LiteralDraft.literal (fun j => (ports K j:ℤ))) := by
  intro V _ _
  exact compact_no_zero_iff K (hr V)

/-- The exact positive-82 parent bridge remains an external Lean hypothesis;
gamma/model-port/provider obligations are inherited through the 90 client. -/
theorem polynomialBridge (K : ℕ) (hr : ForcedR K)
    (h82 : PolynomialBridge (positiveShift (Residue82LiteralDraft.literal (fun j => (ports K j:ℤ))))) :
    PolynomialBridge (ResidueFoldP89Draft.literal (fun j => (ports K j:ℤ))) :=
  HAExpressionNoZeroEquiv.bridge _ _ (compact_sameNoZero K hr)
    (Residue90To82TransportDraft.polynomialBridge K h82)

theorem native_equivalence (K : ℕ) (hr : ForcedR K)
    (h82 : PolynomialBridge (positiveShift (Residue82LiteralDraft.literal (fun j => (ports K j:ℤ))))) : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (ResidueFoldP89Draft.literal (fun j => (ports K j:ℤ))) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (polynomialBridge K hr h82)
end DiophantineConsistency.Residue89To90TransportDraft
#print axioms DiophantineConsistency.Residue89To90TransportDraft.compact_no_zero_iff
#print axioms DiophantineConsistency.Residue89To90TransportDraft.native_equivalence
'''
t=P/'Residue89To90Transport.lean.src'
if '--initialize' in sys.argv:t.write_text(s)
else:assert t.read_text()==s
print(json.dumps({'scope':'source transport reconstruction, no Lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'residual_relations':4,'shift_coordinate':8},sort_keys=True,indent=2))
