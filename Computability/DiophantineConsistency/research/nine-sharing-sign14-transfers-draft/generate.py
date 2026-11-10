#!/usr/bin/env python3
"""Generate source-only supplied-inner sign14 residual transfers."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;src=here.parent/'nine-sharing-sign14-tau-candidate/seed.json';raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';d=json.loads(raw);names=[r['gate'] for r in d['residuals']];assert names==['Dc2','N0','Nt','Na','scaled_Ns'];oldidx=[0,2,3,4,5]
shared=', '.join(f'SharingSeed{fam}.shared{i:02}' for fam,count in [('15Degree124',40),('14Degree124',44)] for i in range(count))
for i,n in enumerate(names):
 j=oldidx[i];assert n.isidentifier();p=here/f'Sign14Transfer{i:02}.lean'
 if p.exists():raise SystemExit('refusing overwrite '+str(p))
 oldclaim=f'SharingSeed15Degree124.firstResidual p = old{n} p' if j==0 else f'((SharingSeed15Degree124.remainingResiduals p).drop {j-1}).head? = some (old{n} p)'
 newclaim=f'SharingSeed14Degree124.firstResidual p = new{n} p' if i==0 else f'((SharingSeed14Degree124.remainingResiduals p).drop {i-1}).head? = some (new{n} p)'
 p.write_text(f'''import DiophantineConsistency.Sign14Coordinate

/-! SOURCE-ONLY supplied-inner residual transfer. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14Transfers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {{V : Type}} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def old{n} (p : Fin 4 → ℤ) : Expr (Fin 16) := SharingSeed15Degree124.row{j:02} p
def new{n} (p : Fin 4 → ℤ) : Expr (Fin 15) := SharingSeed14Degree124.row{i:02} p

theorem old_{n}_row (p : Fin 4 → ℤ) :
    {oldclaim} := by rfl

theorem new_{n}_row (p : Fin 4 → ℤ) :
    {newclaim} := by rfl

theorem {n}_eval (p : Fin 4 → ℤ) (v : Fin 15 → V) (gap : V)
    (hg : ι gap = (SharingSeed14Degree124.shared36 p).evalRing (fun j => ι (v j))) :
    (old{n} p).evalRing (fun j => ι (Sign14Coordinate.lift v gap j)) =
      (new{n} p).evalRing (fun j => ι (v j)) := by
  simp [old{n}, new{n}, SharingSeed15Degree124.row{j:02}, SharingSeed14Degree124.row{i:02},
    {shared}, Sign14Coordinate.lift, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul,
    map_ofNat, hg]
end DiophantineConsistency.Sign14Transfers
#print axioms DiophantineConsistency.Sign14Transfers.{n}_eval
''')
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','transfers':len(names),'scope':'No Lean compilation or representative existence.'},indent=2,sort_keys=True))
