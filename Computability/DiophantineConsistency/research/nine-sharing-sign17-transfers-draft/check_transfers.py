#!/usr/bin/env python3
"""Check conditional transfer aliases/offsets against pinned seed orders."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;r=here.parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();old=r/'nine-sharing-sign18-degree94-root-candidate/seed.json';new=r/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';assert sha(old)=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb';assert sha(new)=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac';a=json.loads(old.read_text())['residuals'];b=json.loads(new.read_text())['residuals'];assert a[6]['gate']=='V2minusY2';indices=[i for i in range(len(a)) if i!=6];assert [a[i]['gate'] for i in indices]==[x['gate'] for x in b] and len(b)==8
files={}
for i,(j,row) in enumerate(zip(indices,b)):
 n=row['gate'];p=here/f'Sign17Transfer{i:02}.lean';s=p.read_text();assert s.startswith('import DiophantineConsistency.Sign17Coordinate\n')
 assert f'def old{n} (p : Fin 4 → ℤ) : Expr (Fin 19) := SharingSeed18Degree94.row{j:02} p' in s
 assert f'def new{n} (p : Fin 4 → ℤ) : Expr (Fin 18) := SharingSeed17Degree96.row{i:02} p' in s
 oldclaim=f'SharingSeed18Degree94.firstResidual p = old{n} p' if j==0 else f'((SharingSeed18Degree94.remainingResiduals p).drop {j-1}).head? = some (old{n} p)';assert oldclaim in s
 newclaim=f'SharingSeed17Degree96.firstResidual p = new{n} p' if i==0 else f'((SharingSeed17Degree96.remainingResiduals p).drop {i-1}).head? = some (new{n} p)';assert newclaim in s
 assert f'theorem {n}_eval ' in s and '(hg : ι gap = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17))' in s and 'sorry' not in s and 'admit' not in s;files[p.name]=sha(p)
print(json.dumps({'status':'PASS_SOURCE_ROW_MAPPING_ONLY','transfers':len(b),'files':files,'scope':'Pinned seed order and staged aliases, not Lean compilation or representative existence.'},indent=2,sort_keys=True))
