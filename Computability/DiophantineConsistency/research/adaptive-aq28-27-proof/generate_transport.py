#!/usr/bin/env python3
"""Prepare model witness transport and native bridge sources; Lean replay pending."""
import hashlib
from pathlib import Path
D=Path(__file__).resolve().parent; ROOT=D.parents[1]; SOURCE=ROOT/'Lean/DiophantineConsistency'; L=D/'draft-src'; L.mkdir(exist_ok=True)
PINS={'AdaptiveAQ29Transport':'a29adc619090a7348f1d41787d4440954e96163ff849917cdc2d7ff6562381e4',
      'AdaptiveAQ29':'4c3501a5d893bf008dfe1f8c517f7b499cb3539a5e035d53bfbae97969534c41',
      'AdaptiveAQ29Checks':'c731095a6f31a21f644b25ca1aaf5bf1fe035f136cc142ee50eea121476ec379',
      'IPRAAQ29Native':'5cea54beebebbeee6d3ed7e4d412df199d0de454c5378cbb2425a8740f4ff9ee',
      'IPRAAQ29NativeChecks':'e818eeddf99ac7ffde043fe0f91a9ca891689810467cc8df1bb1fb845eba701f'}
TEMPLATES={name:(SOURCE/(name+'.lean')).read_bytes() for name in PINS}
for name,pin in PINS.items():
 if hashlib.sha256(TEMPLATES[name]).hexdigest()!=pin:
  raise ValueError(('AQ29 template drift',name))
configs=[(28,29,26,17,'.var 14 * .var 14','v 14 * v 14','mul_pos (hv 14) (hv 14)'),(27,28,25,16,'.var 17 * (.var 17 + (.var 9 + .var 10))','v 17 * (v 17 + (v 9 + v 10))','mul_pos (hv 17) (add_pos (hv 17) (add_pos (hv 9) (hv 10)))'),(26,27,25,16,'.var 18 * .var 4','v 18 * v 4','mul_pos (hv 18) (hv 4)')]
for n,parent,removed,ri,expr,value,posproof in configs:
 m=n-9; pm=m+1
 project=','.join(f'v {j}' for j in range(parent) if j!=removed)
 extend=','.join(value if j==removed else f'v {j if j<removed else j-1}' for j in range(parent))
 fill=','.join(expr if j==removed else f'.var {j if j<removed else j-1}' for j in range(parent))
 maps=f'''import DiophantineConsistency.AdaptiveAQ{n}Zeros
import DiophantineConsistency.AdaptiveAQ{parent}Zeros
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ{n}Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {{V : Type*}} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def project (v : Fin {parent} → V) : Fin {n} → V := ![{project}]
def extend (v : Fin {n} → V) : Fin {parent} → V := ![{extend}]
omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem project_pos (v : Fin {parent} → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < project v i := by
  intro i
  fin_cases i <;> exact hv _
theorem extend_pos (v : Fin {n} → V) (hv : ∀ i, 0 < v i) : ∀ i, 0 < extend v i := by
  intro i
  fin_cases i <;> dsimp [extend] <;> first | exact hv _ | exact {posproof}
#print axioms project_pos
#print axioms extend_pos
end DiophantineConsistency.AdaptiveAQ{n}Maps
'''
 (L/f'AdaptiveAQ{n}Maps.lean').write_text(maps)
 t=TEMPLATES['AdaptiveAQ29Transport'].decode()
 # Preserve the common proof vocabulary and replace the generated bodies below.
 header=t[:t.index('def fill')].replace('AdaptiveAQ29',f'AdaptiveAQ{n}').replace('AdaptiveAQ30',f'AdaptiveAQ{parent}')
 pair={28:'(.var 14 * .var 14)',27:'(.var 17 * (.var 17 + (.var 9 + .var 10)))',26:'(.var 18 * .var 4)'}[n]
 head=f'''def fill : Fin {parent} → Expr (Fin {n}) := ![{fill}]
theorem extend_inputs (v : Fin {n} → V) :
    ∀ i, Equivalent (splitEval (.var i) (extend v)) (splitEval (fill i) v) := by
  intro i
  fin_cases i <;> try exact equivalent_refl _
  simp [extend,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent]

theorem project_inputs (p : Fin 4 → ℤ) (v : Fin {parent} → V)
    (hz : InternalZero (AdaptiveAQ{parent}Literal.literal p) v) :
    ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill i) (project v)) := by
  have hall := (AdaptiveAQ{parent}Zeros.sum_zero p v).mp hz
  have h9 := hall {ri}
  change InternalZero (.var {removed} - {pair}) v at h9
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h9
  intro i
  fin_cases i <;> try exact equivalent_refl _
  simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent] using h9
#print axioms extend_inputs
#print axioms project_inputs
theorem residual_equiv (p : Fin 4 → ℤ) (v : Fin {parent} → V) (w : Fin {n} → V)
    (hinputs : ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill i) w)) (i : Fin {pm}) :
    InternalZero (AdaptiveAQ{parent}Zeros.residuals p i) v ↔
    InternalZero ((AdaptiveAQ{parent}Zeros.residuals p i).subst fill) w := by
  have h := subst_equiv_hetero (AdaptiveAQ{parent}Zeros.residuals p i) (fun i => .var i) fill v w hinputs
  simpa only [DiophantineConsistency.AdaptiveAQ30Transport.subst_id,InternalZero,splitEval] using equivalent_zero_iff h

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin {n} → V)
    (hz : InternalZero (AdaptiveAQ{n}Literal.literal p) v) :
    InternalZero (AdaptiveAQ{parent}Literal.literal p) (extend v) := by
  have hall := (AdaptiveAQ{n}Zeros.sum_zero p v).mp hz
  apply (AdaptiveAQ{parent}Zeros.sum_zero p (extend v)).mpr
  intro i
  apply (residual_equiv p (extend v) v (extend_inputs v) i).mpr
  fin_cases i
'''
 for j in range(pm):
  if j==ri: head+=f'  · change InternalZero ({pair} - {pair}) v\n    simp only [InternalZero]\n    exact add_comm _ _\n'
  else:
   q=j if j<ri else j-1
   head+=f'  · change InternalZero (AdaptiveAQ{n}Zeros.residuals p {q}) v\n    exact hall {q}\n'
 head+=f'''
theorem project_zero (p : Fin 4 → ℤ) (v : Fin {parent} → V)
    (hz : InternalZero (AdaptiveAQ{parent}Literal.literal p) v) :
    InternalZero (AdaptiveAQ{n}Literal.literal p) (project v) := by
  have hall := (AdaptiveAQ{parent}Zeros.sum_zero p v).mp hz
  apply (AdaptiveAQ{n}Zeros.sum_zero p (project v)).mpr
  intro i
  fin_cases i
'''
 for j in range(m):
  q=j if j<ri else j+1
  head+=f'  · have h := (residual_equiv p v (project v) (project_inputs p v hz) {q}).mp (hall {q})\n    change InternalZero (AdaptiveAQ{n}Zeros.residuals p {j}) (project v) at h\n    exact h\n'
 head+=f'#print axioms extend_zero\n#print axioms project_zero\nend DiophantineConsistency.AdaptiveAQ{n}Transport\n'
 (L/f'AdaptiveAQ{n}Transport.lean').write_text(header+head)
 model=TEMPLATES['AdaptiveAQ29'].decode().replace('AdaptiveAQ30','PARENT_ADAPTIVE').replace('AdaptiveAQ29',f'AdaptiveAQ{n}').replace('PARENT_ADAPTIVE',f'AdaptiveAQ{parent}').replace('Fin 30','PARENT_FIN').replace('Fin 29',f'Fin {n}').replace('PARENT_FIN',f'Fin {parent}')
 (L/f'AdaptiveAQ{n}.lean').write_text(model)
 checks=TEMPLATES['AdaptiveAQ29Checks'].decode().replace('AdaptiveAQ29',f'AdaptiveAQ{n}')
 (L/f'AdaptiveAQ{n}Checks.lean').write_text(checks)
 native=TEMPLATES['IPRAAQ29Native'].decode().replace('IPRAAQ30Native','PARENT_NATIVE').replace('AdaptiveAQ29',f'AdaptiveAQ{n}').replace('IPRAAQ29Native',f'IPRAAQ{n}Native').replace('PARENT_NATIVE',f'IPRAAQ{parent}Native').replace('bridge30','PARENT_BRIDGE').replace('bridge29',f'bridge{n}').replace('PARENT_BRIDGE',f'bridge{parent}').replace('sameNoZero',f'sameNoZero').replace('Fin 29',f'Fin {n}').replace('twenty-nine',str(n))
 (L/f'IPRAAQ{n}Native.lean').write_text(native)
 nativechecks=TEMPLATES['IPRAAQ29NativeChecks'].decode().replace('AdaptiveAQ29',f'AdaptiveAQ{n}').replace('IPRAAQ29Native',f'IPRAAQ{n}Native').replace('bridge29',f'bridge{n}')
 (L/f'IPRAAQ{n}NativeChecks.lean').write_text(nativechecks)
 print(f'Prepared AQ{n} transport and native sources; compilation pending')
