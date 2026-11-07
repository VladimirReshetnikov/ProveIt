#!/usr/bin/env python3
"""Check 28→31 source coordinates and all external AST substitutions; no Lean."""
import hashlib,json,re
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];s=(P/'SharingSeed28BridgeDraft.lean').read_text()
def row(name):
 m=re.search(r'\bdef '+name+r'\b[^\n]*\n\s*!\[(.*?)\]',s,re.S);assert m;return [x.strip() for x in m.group(1).split(',')]
a,b=row('lift'),row('drop');assert a==[f'v {i}' for i in range(16)]+['(v 9 + 1) * (beta * (v 1 + 1) + 1)']+[f'v {i}' for i in range(16,22)]+['(v 18 + (v 11 + 1)) ^ 2']+[f'v {i}' for i in range(22,28)]+['(v 27) ^ 2','v 28'];assert b==[f'v {i}' for i in range(16)]+[f'v {i}' for i in range(17,23)]+[f'v {i}' for i in range(24,30)]+['v 31']
old=json.loads((D/'research/nine-sharing-sign31-sextic-candidate/seed.json').read_text());new=json.loads((D/'research/nine-sharing-sign28-sextic-candidate/seed.json').read_text());var=lambda i:['var',i];one=['num',1];add=lambda x,y:['add',x,y];mul=lambda x,y:['mul',x,y]
x=mul(add(var(9),one),add(mul(['port','beta'],add(var(1),one)),one));cbase=add(var(18),add(var(11),one));c2=mul(cbase,cbase);s2=mul(var(27),var(27));mapping=[var(i) for i in range(16)]+[x]+[var(i) for i in range(16,22)]+[c2]+[var(i) for i in range(22,28)]+[s2,var(28)];assert len(mapping)==32

def subst(t):
 if t[0]=='var':return mapping[t[1]]
 if t[0] in ('num','port'):return t
 return [t[0],subst(t[1]),subst(t[2])]
assert len(old['residuals'])==22 and len(new['residuals'])==19
oldby={r['gate']:r['expr'] for r in old['residuals']};newby={r['gate']:r['expr'] for r in new['residuals']};assert len(oldby)==22 and len(newby)==19 and set(oldby)-set(newby)=={'X','c2','normalized_S2'}
for gate,expr in newby.items():assert subst(oldby[gate])==expr,gate
for gate,index in [('X',16),('c2',23),('normalized_S2',30)]:
 t=oldby[gate];assert t[0]=='sub' and t[1]==['var',index] and subst(t[1])==subst(t[2]),gate
for term in ['((p 0 : ℤ) : DiffRing V) = ι beta →','InternalZero (SharingSeed28Sextic.seed p) v','InternalZero (SharingSeed31Sextic.seed p) (lift beta v)','InternalZero (SharingSeed31Sextic.seed p) v','InternalZero (SharingSeed28Sextic.seed p) (drop v)']:assert term in s
assert 'theorem ' not in s and not re.search(r'\b(sorry|admit)\b',s)
out={'status':'pass','scope':'source text and external AST substitution only; no Lean parsing, elaboration or proof','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'lift_entries':len(a),'drop_entries':len(b),'removed_old_coordinates':[16,23,30],'reconstructed_rows':['X','c2','normalized_S2'],'surviving_rows_checked':len(newby),'distinguished_coordinate_zero_preserved':True,'open_targets':['ForwardTarget','BackwardTarget']};(P/'bridge-result.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,sort_keys=True))
