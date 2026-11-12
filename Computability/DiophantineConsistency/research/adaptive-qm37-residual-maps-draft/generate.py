#!/usr/bin/env python3
"""Generate inert candidate residual and zero-map proofs; no Lean/staging."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];base=D/'research/adaptive-qm37-conditional-model-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
par=pin(D/'research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38Residuals.lean.src','d0bb6ab27fbd9f70c5e4faf529a725ae065bf9787b570a8c675c38d21460fa97')
chi=pin(base/'AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
pin(base/'AdaptiveQM37ConditionalTransfer.lean.src','be810ba3342ba05423e42e70eceff065809ba0380b804b79060b17ae73415566')
pin(base/'AdaptiveQM37DifferenceWitness.lean.src','b65647fb73619d6f52e166ae61233854a47e9f968174481f321f44bcdf915c80')
new=json.loads(pin(D/'research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'))
def vector(s):
 x=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(x)==1;return x[0].split(',')
a=vector(par);b=vector(chi);assert len(a)==29 and len(b)==28 and a[2]==b[2]=='auxResidual' and a[4]=='squareDifference' and a[21]=='ySquareDifference' and b[4]=='differenceEquality'
common=[]
for j,n in enumerate(b):
 if j in (2,4):continue
 assert n in a;common.append((a.index(n),j,n))
assert len(common)==26 and set(a)-set(b)=={'squareDifference','ySquareDifference'}
header='''import AdaptiveQM37ConditionalTransfer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Source-only residual comparison and model-map proof proposal; no Lean. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM37ResidualMapsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open AdaptiveQM37ConditionalTransferDraft AdaptiveQM37DifferenceWitnessDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''
tac='''  simp [AdaptiveQM38ResidualsDraft.residuals, AdaptiveQM37ResidualsDraft.residuals,
    extend, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add, map_mul] <;> ring
'''
lemmas=[]
for i,j,n in common:
 lemmas.append(f'''/-- Parent residual {i}, child residual {j}: {n}. -/
theorem same{j:02d} (p : Fin 4 → ℤ) (v : Fin 37 → V) :
    (AdaptiveQM38ResidualsDraft.residuals p {i}).evalRing (fun k => ι (extend v k)) =
      (AdaptiveQM37ResidualsDraft.residuals p {j}).evalRing (fun k => ι (v k)) := by
'''+tac+'\n')
for i in (4,21):
 lemmas.append(f'''/-- Parent stored-square residual {i} vanishes on extension. -/
theorem dropped{i:02d} (p : Fin 4 → ℤ) (v : Fin 37 → V) :
    (AdaptiveQM38ResidualsDraft.residuals p {i}).evalRing (fun k => ι (extend v k)) = 0 := by
'''+tac+'\n')
lemmas.append('''/-- The only altered retained residual differs by Q times the new
positive-difference residual. -/
theorem aux_relation (p : Fin 4 → ℤ) (v : Fin 37 → V) :
    (AdaptiveQM38ResidualsDraft.residuals p 2).evalRing (fun k => ι (extend v k)) =
      (AdaptiveQM37ResidualsDraft.residuals p 2).evalRing (fun k => ι (v k)) +
        ι (v 30) * (AdaptiveQM37ResidualsDraft.residuals p 4).evalRing (fun k => ι (v k)) := by
'''+tac+'''
/-- Restoring the squares after projection gives back a parent satisfying the
parent square residuals. -/
theorem extend_project (v : Fin 38 → V) (d : V)
    (hs : v 13=v 25*v 25) (hy : v 30=v 11*v 11) :
    extend (project v d)=v := by
  funext i
  fin_cases i <;> simp [extend, project, hs, hy]

/-- The projected new difference residual is zero under the natural additive
square-difference equality; no signed natural subtraction is used. -/
theorem project_difference (p : Fin 4 → ℤ) (v : Fin 38 → V) (d : V)
    (hd : v 11*v 11=v 25*v 25+d) :
    InternalZero (AdaptiveQM37ResidualsDraft.residuals p 4) (project v d) := by
  rw [ModelDifferenceRing.internalZero_iff]
  have h := congrArg (ι : V →+* DiffRing V) hd
  simp only [map_add,map_mul] at h
  simp [AdaptiveQM37ResidualsDraft.residuals, project,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat,
    map_add, map_mul, map_one] <;> linear_combination -h

''')
# Assemble the 29 parent residual zeros from the 28 child zeros.
E='''/-- A child zero lifts to a parent zero, conditional only on the proposed
residual identities above, all of which are in this same source. -/
theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 37 → V)
    (hz : InternalZero (AdaptiveQM37LiteralDraft.literal p) v) :
    InternalZero (AdaptiveQM38LiteralDraft.literal p) (extend v) := by
  have hc := (AdaptiveQM37ResidualZerosDraft.all_residuals p v).mp hz
  have hd := (ModelDifferenceRing.internalZero_iff _ _).mp (hc 4)
  apply (AdaptiveQM38ResidualZerosDraft.all_residuals p (extend v)).mpr
  intro i
  fin_cases i
'''
byParent={i:j for i,j,n in common}
for i in range(29):
 if i in (4,21):
  E+=f'''  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr
    exact dropped{i:02d} p v
'''
 elif i==2:
  E+='''  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr
    rw [aux_relation p v, hd, mul_zero, add_zero]
    exact (ModelDifferenceRing.internalZero_iff _ _).mp (hc 2)
'''
 else:
  j=byParent[i];E+=f'''  · apply (ModelDifferenceRing.internalZero_iff _ _).mpr
    rw [same{j:02d} p v]
    exact (ModelDifferenceRing.internalZero_iff _ _).mp (hc {j})
'''
# Assemble 28 child residual zeros from parent zeros, after project/lift identity.
E+='''
/-- A parent zero and the explicit nonnegative difference project to a child
zero. Existence of the difference is supplied separately by parent_difference. -/
theorem project_zero (p : Fin 4 → ℤ) (v : Fin 38 → V) (d : V)
    (hz : InternalZero (AdaptiveQM38LiteralDraft.literal p) v)
    (hd : v 11*v 11=v 25*v 25+d) :
    InternalZero (AdaptiveQM37LiteralDraft.literal p) (project v d) := by
  have hp := (AdaptiveQM38ResidualZerosDraft.all_residuals p v).mp hz
  obtain ⟨hs,hy⟩ := parent_square_values p v hz
  have hlift := extend_project v d hs hy
  have hdiff := project_difference p v d hd
  have hdiffR := (ModelDifferenceRing.internalZero_iff _ _).mp hdiff
  apply (AdaptiveQM37ResidualZerosDraft.all_residuals p (project v d)).mpr
  intro i
  fin_cases i
'''
byChild={j:i for i,j,n in common}
for j in range(28):
 if j==4:E+='  · exact hdiff\n'
 elif j==2:
  E+='''  · have hparent : InternalZero (AdaptiveQM38ResidualsDraft.residuals p 2)
        (extend (project v d)) := by simpa only [hlift] using hp 2
    have hr := (ModelDifferenceRing.internalZero_iff _ _).mp hparent
    rw [aux_relation p (project v d), hdiffR, mul_zero, add_zero] at hr
    exact (ModelDifferenceRing.internalZero_iff _ _).mpr hr
'''
 else:
  i=byChild[j];E+=f'''  · have hparent : InternalZero (AdaptiveQM38ResidualsDraft.residuals p {i})
        (extend (project v d)) := by simpa only [hlift] using hp {i}
    have hr := (ModelDifferenceRing.internalZero_iff _ _).mp hparent
    rw [same{j:02d} p (project v d)] at hr
    exact (ModelDifferenceRing.internalZero_iff _ _).mpr hr
'''
E+='''
/-- Proposed discharge of the earlier explicit graph obligations. -/
theorem graphZeroObligations : GraphZeroObligations := by
  intro V _ _
  constructor
  · intro v d _ hz hd
    exact project_zero CurrentWindowCarry2011.ports v d hz hd
  · intro v _ hz
    exact extend_zero CurrentWindowCarry2011.ports v hz

end DiophantineConsistency.AdaptiveQM37ResidualMapsDraft
#print axioms DiophantineConsistency.AdaptiveQM37ResidualMapsDraft.aux_relation
#print axioms DiophantineConsistency.AdaptiveQM37ResidualMapsDraft.project_difference
#print axioms DiophantineConsistency.AdaptiveQM37ResidualMapsDraft.extend_zero
#print axioms DiophantineConsistency.AdaptiveQM37ResidualMapsDraft.project_zero
#print axioms DiophantineConsistency.AdaptiveQM37ResidualMapsDraft.graphZeroObligations
'''
text=header+''.join(lemmas)+E
(P/'AdaptiveQM37ResidualMaps.lean.src').write_text(text)
print(json.dumps({'scope':'generated source-only proposed residual and zero-map proofs; no Lean','common_residual_pairs':len(common),'special_auxiliary':True,'dropped_parent_residuals':[4,21],'new_difference_residual':4,'proof_source_sha256':hashlib.sha256(text.encode()).hexdigest()},sort_keys=True,indent=2))
