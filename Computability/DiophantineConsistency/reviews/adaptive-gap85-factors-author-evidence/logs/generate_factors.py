"""Generate exact four-factor projections of the pinned 85-gate literal."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;raw=(D/'candidate.json').read_bytes();assert hashlib.sha256(raw).hexdigest()=='c2c2e1bbb267bdc155536c5b3df9641f8faff97dab4b549a1d514d671ebdea00';j=json.loads(raw);rows=j['source'];assert rows[-4:]==[['g86','*','F0','F1'],['g87','*','Fa','g86'],['g88','*','Fs','g87'],['P13','-','g88',1]]
lines=[]
for i,n in enumerate(j['witnesses']):lines.append(f'  let {n} : Expr (Fin 13) := .var {i}')
for i,n in enumerate(j['fixed_numerals']):lines.append(f'  let {n} : Expr (Fin 13) := .constant (p {i})')
for n,op,a,b in rows[:-4]:lines.append(f'  let {n} := {a} {op} {b}')
lines.append('  (F0,F1,Fa,Fs)')
s='''import DiophantineConsistency.AdaptiveGap85Literal

/-! Exact factor projections of the generated 85 literal. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Factors
open AdaptiveGap85Literal

def factors (p : Fin 4 → ℤ) : Expr (Fin 13) × Expr (Fin 13) × Expr (Fin 13) × Expr (Fin 13) :=
'''+ '\n'.join(lines)+'''

theorem expression_factors (p : Fin 4 → ℤ) :
    expressionAt85 p = (factors p).2.2.2 * ((factors p).2.2.1 *
      ((factors p).1 * (factors p).2.1)) - 1 := by
  rfl
end DiophantineConsistency.AdaptiveGap85Factors
'''
out=D.parents[1]/'Lean/DiophantineConsistency/AdaptiveGap85Factors.lean';out.write_text(s);print('wrote',out)
