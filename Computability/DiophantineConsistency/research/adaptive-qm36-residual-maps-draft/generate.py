#!/usr/bin/env python3
"""Generate inert QM36 residual and model-map proof proposals; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];B=D/'research/adaptive-qm36-conditional-model-draft';C=D/'research/adaptive-qm37-conditional-model-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
old=pin(C/'AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
new=pin(B/'AdaptiveQM36Residuals155.lean.src','03c99c18fc52e185bf8c334ce3ab62afb40c9f0d91d7bdc2cd5e695263dfae95')
pin(B/'AdaptiveQM36ConditionalTransfer.lean.src','865a63bdcb03a5f7dc1845bc5af0217529b3d549e7a6e67b73f0f1cf447bc754')
pin(B/'AdaptiveQM36ParentSlots.lean.src','69bf3f920031a0451740b04c48a68a3ee4edd5708aed84cf85066bf24a23ac78')
pin(B/'AdaptiveQM36ResidualZeros.lean.src','716de991c36f462e2a3d0e7e65f2909e2db66923abb185ccb9674a11275a426e')
def vec(s):
 x=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(x)==1;return x[0].split(',')
a=vec(old);b=vec(new);assert len(a)==28 and len(b)==27 and a[11]=='productDifference' and a[26]=='gammaProductDifference' and b[11]=='combinedEquality' and a[15]==b[15]=='dDifference'
common=[(a.index(n),j,n) for j,n in enumerate(b) if j not in (11,15)];assert len(common)==25
head='''import AdaptiveQM36ConditionalTransfer
import AdaptiveQM36ParentSlots
import AdaptiveQM36ResidualZeros
import AdaptiveQM37ResidualZeros
import Mathlib.Tactic.Ring

/-! Proposed residual identities and beta-represented graph maps. All source
here and inherited dependencies remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM36ResidualMapsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AdaptiveQM36ConditionalTransferDraft AdaptiveQM36ParentSlotsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
tac='''  simp [AdaptiveQM37ResidualsDraft.residuals, AdaptiveQM36Residuals155Draft.residuals,
    extend, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add, map_mul, hbeta] <;> ring
'''
lemmas=[]
for i,j,n in common:
 lemmas.append(f'''/-- Parent residual {i}, child residual {j}: {n}. -/
theorem same{j:02d} (p : Fin 4 → ℤ) (beta : V) (v : Fin 36 → V)
    (hbeta : ((p 0 : ℤ) : DiffRing V)=ι beta) :
    (AdaptiveQM37ResidualsDraft.residuals p {i}).evalRing (fun k => ι (extend beta v k)) =
      (AdaptiveQM36Residuals155Draft.residuals p {j}).evalRing (fun k => ι (v k)) := by
'''+tac+'\n')
for i in (11,26):
 lemmas.append(f'''/-- Old product residual {i} vanishes under the represented lift. -/
theorem dropped{i:02d} (p : Fin 4 → ℤ) (beta : V) (v : Fin 36 → V)
    (hbeta : ((p 0 : ℤ) : DiffRing V)=ι beta) :
    (AdaptiveQM37ResidualsDraft.residuals p {i}).evalRing (fun k => ι (extend beta v k)) = 0 := by
'''+tac+'\n')
lemmas.append('''/-- The changed main-root binding differs by H times the combined residual. -/
theorem d_relation (p : Fin 4 → ℤ) (beta : V) (v : Fin 36 → V)
    (hbeta : ((p 0 : ℤ) : DiffRing V)=ι beta) :
    (AdaptiveQM37ResidualsDraft.residuals p 15).evalRing (fun k => ι (extend beta v k)) =
      (AdaptiveQM36Residuals155Draft.residuals p 15).evalRing (fun k => ι (v k)) +
        (3+4*(ι (v 28)+ι (v 7))) *
          (AdaptiveQM36Residuals155Draft.residuals p 11).evalRing (fun k => ι (v k)) := by
'''+tac+'''
/-- Reconstruct a parent when its two positive product slots are correct. -/
theorem extend_project (beta : V) (v : Fin 37 → V)
    (h20 : v 20=v 28*(1+v 0*beta)) (h33 : v 33=v 15*v 12) :
    extend beta (project v)=v := by
  funext i
  fin_cases i <;> simp [extend, project, h20, h33]

/-- On a parent zero the combined child residual vanishes. -/
theorem project_combined (p : Fin 4 → ℤ) (beta : V) (v : Fin 37 → V)
    (hbeta : ((p 0 : ℤ) : DiffRing V)=ι beta)
    (hz : InternalZero (AdaptiveQM37LiteralDraft.literal p) v) :
    InternalZero (AdaptiveQM36Residuals155Draft.residuals p 11) (project v) := by
  have h20 := product_slot p beta v hbeta hz
  have h33 := gamma_slot p v hz
  rw [ModelDifferenceRing.internalZero_iff]
  simp [AdaptiveQM36Residuals155Draft.residuals, project, h20, h33, hbeta,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, map_add, map_mul] <;> ring

''')
E='''/-- A child zero extends to a parent zero, under the exact beta cast. -/
theorem extend_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 36 → V)
    (hbeta : ((p 0 : ℤ) : DiffRing V)=ι beta)
    (hz : InternalZero (AdaptiveQM36Literal155Draft.literal p) v) :
    InternalZero (AdaptiveQM37LiteralDraft.literal p) (extend beta v) := by
  have hc := (AdaptiveQM36ResidualZerosDraft.all_residuals p v).mp hz
  have hd := (ModelDifferenceRing.internalZero_iff _ _).mp (hc 11)
  apply (AdaptiveQM37ResidualZerosDraft.all_residuals p (extend beta v)).mpr
  intro i
  fin_cases i
'''
byold={i:j for i,j,n in common}
for i in range(28):
 if i in (11,26):E+=f'''  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr
    exact dropped{i:02d} p beta v hbeta
'''
 elif i==15:E+='''  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr
    rw [d_relation p beta v hbeta, hd, mul_zero, add_zero]
    exact (ModelDifferenceRing.internalZero_iff _ _).mp (hc 15)
'''
 else:
  j=byold[i];E+=f'''  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr
    rw [same{j:02d} p beta v hbeta]
    exact (ModelDifferenceRing.internalZero_iff _ _).mp (hc {j})
'''
E+='''
/-- A parent zero projects to a child zero under the exact beta cast. -/
theorem project_zero (p : Fin 4 → ℤ) (beta : V) (v : Fin 37 → V)
    (hbeta : ((p 0 : ℤ) : DiffRing V)=ι beta)
    (hz : InternalZero (AdaptiveQM37LiteralDraft.literal p) v) :
    InternalZero (AdaptiveQM36Literal155Draft.literal p) (project v) := by
  have hp := (AdaptiveQM37ResidualZerosDraft.all_residuals p v).mp hz
  have h20 := product_slot p beta v hbeta hz
  have h33 := gamma_slot p v hz
  have hlift := extend_project beta v h20 h33
  have hcombined := project_combined p beta v hbeta hz
  have hcombinedR := (ModelDifferenceRing.internalZero_iff _ _).mp hcombined
  apply (AdaptiveQM36ResidualZerosDraft.all_residuals p (project v)).mpr
  intro i
  fin_cases i
'''
bynew={j:i for i,j,n in common}
for j in range(27):
 if j==11:E+='  · exact hcombined\n'
 elif j==15:E+='''  · have hparent : InternalZero (AdaptiveQM37ResidualsDraft.residuals p 15)
        (extend beta (project v)) := by simpa only [hlift] using hp 15
    have hr := (ModelDifferenceRing.internalZero_iff _ _).mp hparent
    rw [d_relation p beta (project v) hbeta, hcombinedR, mul_zero, add_zero] at hr
    exact (ModelDifferenceRing.internalZero_iff _ _).mpr hr
'''
 else:
  i=bynew[j];E+=f'''  · have hparent : InternalZero (AdaptiveQM37ResidualsDraft.residuals p {i})
        (extend beta (project v)) := by simpa only [hlift] using hp {i}
    have hr := (ModelDifferenceRing.internalZero_iff _ _).mp hparent
    rw [same{j:02d} p beta (project v) hbeta] at hr
    exact (ModelDifferenceRing.internalZero_iff _ _).mpr hr
'''
E+='''
/-- The earlier fixed-port graph obligations, conditional only on these
unelaborated residual/slot source proofs. -/
theorem graphZeroObligations : GraphZeroObligations := by
  intro V _ _ beta hbeta
  constructor
  · intro v _ hz
    exact project_zero CurrentWindowCarry2011.ports beta v hbeta hz
  · intro v _ hz
    exact extend_zero CurrentWindowCarry2011.ports beta v hbeta hz

end DiophantineConsistency.AdaptiveQM36ResidualMapsDraft
#print axioms DiophantineConsistency.AdaptiveQM36ResidualMapsDraft.d_relation
#print axioms DiophantineConsistency.AdaptiveQM36ResidualMapsDraft.project_combined
#print axioms DiophantineConsistency.AdaptiveQM36ResidualMapsDraft.extend_zero
#print axioms DiophantineConsistency.AdaptiveQM36ResidualMapsDraft.project_zero
#print axioms DiophantineConsistency.AdaptiveQM36ResidualMapsDraft.graphZeroObligations
'''
text=head+''.join(lemmas)+E;(P/'AdaptiveQM36ResidualMaps.lean.src').write_text(text)
print(json.dumps({'scope':'inert represented-beta residual and graph-map source; no Lean','common_residual_pairs':25,'dropped_parent_residuals':[11,26],'combined_child_residual':11,'special_d_residual':15,'source_sha256':hashlib.sha256(text.encode()).hexdigest()},indent=2,sort_keys=True))
