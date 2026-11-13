#!/usr/bin/env python3
"""Generate source-only conditional sign16 staged residual transfers."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;src=here.parent/'nine-sharing-sign16-degree112-v-candidate/seed.json';raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()=='564ac66abad0fb5e286e5c0c05b5c3cbd05de13e68c9c9ac0b7c3a20a0c0b624';d=json.loads(raw);names=[r['gate'] for r in d['residuals']];assert names==['Dc2','tau','N0','Nt','cTminusR','Na','scaled_Ns'];oldidx=[0,1,2,3,4,6,7]
shared=', '.join(f'SharingSeed{fam}.shared{i:02}' for fam,count in [('17Degree96',35),('16Degree112',37)] for i in range(count))
for i,n in enumerate(names):
 j=oldidx[i];assert n.isidentifier();p=here/f'Sign16Transfer{i:02}.lean'
 if p.exists():raise SystemExit('refusing overwrite '+str(p))
 oldclaim=f'SharingSeed17Degree96.firstResidual p = old{n} p' if j==0 else f'((SharingSeed17Degree96.remainingResiduals p).drop {j-1}).head? = some (old{n} p)'
 newclaim=f'SharingSeed16Degree112.firstResidual p = new{n} p' if i==0 else f'((SharingSeed16Degree112.remainingResiduals p).drop {i-1}).head? = some (new{n} p)'
 p.write_text(f'''import DiophantineConsistency.Sign16Coordinate

/-! SOURCE-ONLY individual conditional signed residual transfer. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign16SharedValues
variable {{V : Type}} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def old{n} (p : Fin 4 → ℤ) : Expr (Fin 18) := SharingSeed17Degree96.row{j:02} p
def new{n} (p : Fin 4 → ℤ) : Expr (Fin 17) := SharingSeed16Degree112.row{i:02} p

theorem old_{n}_row (p : Fin 4 → ℤ) :
    {oldclaim} := by rfl

theorem new_{n}_row (p : Fin 4 → ℤ) :
    {newclaim} := by rfl

theorem {n}_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V) (gap : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hg : ι gap = (ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - ι (C beta v)) :
    (old{n} p).evalRing (fun j => ι (Sign16Coordinate.lift v gap j)) =
      (new{n} p).evalRing (fun j => ι (v j)) := by
  simp [old{n}, new{n}, SharingSeed17Degree96.row{j:02}, SharingSeed16Degree112.row{i:02},
    {shared}, Sign16Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul,
    map_ofNat, C, Y, A, hp0, hg]
end DiophantineConsistency.Sign16Transfers
#print axioms DiophantineConsistency.Sign16Transfers.{n}_eval
''')
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','transfers':len(names),'scope':'No Lean compilation or representative existence.'},indent=2,sort_keys=True))
