#!/usr/bin/env python3
"""One-step syntactic positive-cut survey on the frozen 27 seed."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;source=P.parent/'nine-sharing-sign27-sextic-normalized-root-candidate/seed.json';raw=source.read_bytes();assert hashlib.sha256(raw).hexdigest()=='5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d';s=json.loads(raw);ports=set(s['coefficient_binding']['ports'])
def nat(t):
 if t[0]=='var':return True
 if t[0]=='port':return t[1] in ports
 if t[0]=='num':return type(t[1])==int and t[1]>=0
 return t[0] in ('add','mul') and nat(t[1]) and nat(t[2])
def subst(t,k,r):
 if t[0]=='var':return r if t[1]==k else t
 if t[0] in ('port','num'):return t
 assert t[0] in ('add','sub','mul') and len(t)==3
 return [t[0],subst(t[1],k,r),subst(t[2],k,r)]
def deg(t):
 if t[0]=='var':return 1
 if t[0] in ('port','num'):return 0
 a,b=deg(t[1]),deg(t[2]);return a+b if t[0]=='mul' else max(a,b)
out=[]
for i,row in enumerate(s['residuals']):
 e=row['expr']
 if row['kind']!='positive' or e[0]!='sub' or e[1][0]!='var' or not nat(e[2]):continue
 k=e[1][1];assert subst(e[2],k,['num',-1])==e[2]
 ds=[(r['gate'],deg(subst(r['expr'],k,e[2]))) for j,r in enumerate(s['residuals']) if j!=i];m=max(v for _,v in ds);out.append({'gate':row['gate'],'coordinate':k,'maximum_residual_syntactic_degree':m,'rows_at_maximum':[g for g,v in ds if v==m]})
assert len(out)==7 and all(q['maximum_residual_syntactic_degree']>3 for q in out)
print(json.dumps({'status':'PASS_ONE_STEP_RESTRICTED_SURVEY','source_sha256':hashlib.sha256(raw).hexdigest(),'cases':out,'scope':'positive displayed variable-minus-natural-add/multiply RHS, direct substitution, syntactic degree only; no rewriting, normalization, alternative encodings or semantic impossibility claim'},indent=2,sort_keys=True))
