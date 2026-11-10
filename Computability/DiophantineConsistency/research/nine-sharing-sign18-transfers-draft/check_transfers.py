#!/usr/bin/env python3
"""Check transfer row aliases/offsets against pinned external seed orders."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;r=here.parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();old=r/'nine-sharing-sign19-degree44-y-candidate/seed.json';new=r/'nine-sharing-sign18-degree94-root-candidate/seed.json';assert sha(old)=='01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1';assert sha(new)=='d3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb';a=json.loads(old.read_text())['residuals'];b=json.loads(new.read_text())['residuals'];assert a[0]['gate']=='main_root' and [x['gate'] for x in a[1:]]==[x['gate'] for x in b] and len(b)==9
files={}
for i,row in enumerate(b):
 n=row['gate'];p=here/f'Sign18Transfer{i:02}.lean';s=p.read_text();assert s.startswith('import DiophantineConsistency.Sign18Coordinate\n')
 assert f'def old{n} (p : Fin 4 → ℤ) : Expr (Fin 20) := SharingSeed19Degree44.row{i+1:02} p' in s
 assert f'def new{n} (p : Fin 4 → ℤ) : Expr (Fin 19) := SharingSeed18Degree94.row{i:02} p' in s
 assert f'((SharingSeed19Degree44.remainingResiduals p).drop {i}).head? = some (old{n} p)' in s
 expected=f'SharingSeed18Degree94.firstResidual p = new{n} p' if i==0 else f'((SharingSeed18Degree94.remainingResiduals p).drop {i-1}).head? = some (new{n} p)';assert expected in s
 assert f'theorem {n}_eval ' in s and '(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s and 'sorry' not in s and 'admit' not in s;files[p.name]=sha(p)
print(json.dumps({'status':'PASS_SOURCE_ROW_MAPPING_ONLY','transfers':len(b),'files':files,'scope':'Pinned seed order and staged aliases, not Lean compilation or all-model equivalence.'},indent=2,sort_keys=True))
