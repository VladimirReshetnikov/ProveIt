#!/usr/bin/env python3
"""Independent finite controls; universal divisibility is the README argument."""
import hashlib, json, re, operator, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B')
r = Path(__file__).resolve().parents[2]
p = r / 'research/p64-qcube72-free-main-candidate'
src = (p / 'P64QCube72Free.lean').read_text()
body = src.split('-- BEGIN GENERATED GRAPH',1)[1].split('-- END GENERATED GRAPH',1)[0]
rows = []
for line in body.splitlines():
    if not line.strip(): continue
    m = re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line)
    if not m: raise ValueError(('unparsed graph line', line))
    name,left,op,right = m.groups()
    rows.append([name,op,int(left) if left.isdigit() else left,int(right) if right.isdigit() else right])
j = json.loads((p/'graph.json').read_text())
if len(rows)!=72 or rows!=j['source']: raise ValueError('Lean and JSON graph mismatch')
# Construct actual full natural port constants using the literal digit recipes.
b = 1 << 67
beta = (1 << (67*8807))-1
support = (set(range(943)) | set(range(983,993)) | set(range(1003,1012)) | set(range(1013,1032)) | {1063,1064,1095,2195,3296}) - {1}
low = beta - sum(1 << (67*i) for i in support) - 2*(1 << (67*1063))
digits = [4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
high = sum(x << (67*i) for i,x in enumerate(digits))
if len(digits)!=8807 or len(support)!=985 or not (0<low<beta and 0<high<beta) or beta%3!=1: raise ValueError('port constants')
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
for N in (1,2,3,4,5,8,11,16,27,64,65,97,121,256,997):
    m=N**4
    for J in (1,2):
        q=beta*J+1
        vals={'beta':beta,'K0':q-1,'MC':low,'MF':beta+high,'J':J,'F':1,'alpha':q-2,'z':1,'f':1,'i':1,'T':1,'s':N,'w':1,'t':1,'eta':N,'zeta':1,'y':1,'h':N}
        d={k:v%m for k,v in vals.items()}
        for name,op,x,y in rows:
            d[name]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)%m
        # Separate closed formulas use only residues, including the arbitrary rank.
        Y=q**3*N % m; X=q % m; U=Y*Y % m; k=N+1
        P=X*Y*Y % m; ell=P*k % m; c=(k*Y+N)%m; a=(X*Y+Y)%m
        H=(4*a+3)%m; D=(U*(X+a*c)+H*N)%m
        delta=(a*a+H)%m
        expected={'A0':(1-ell*(ell+k))%m, 'M':(D*D-U*U*(1+delta*c*c))%m,'W':c**4%m,'Na':1%m,'Lt':0,'polynomial':0}
        for key,value in expected.items():
            if d[key]!=value: raise ValueError((N,J,key,d[key],value))
        if N>1 and ((d['A0']-1)%(N*N) or d['M']%(N*N)):
            raise ValueError(('order',N,J))
        if q%3 != (2 if J==1 else 0): raise ValueError(('q class',J))
print(json.dumps({'status':'PASS','graph_rows':len(rows),'positive_N_tested':[1,2,3,4,5,8,11,16,27,64,65,97,121,256,997], 'K_families':2,'actual_full_mask_constants_constructed':True,'scope':'finite controls; symbolic universal proof reviewed separately','pins':{str(f.relative_to(r)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [p/'P64QCube72Free.lean',p/'graph.json',r/'research/p64-qcube72-fixed-mask-all-moduli-controls/check.py']}},sort_keys=True,indent=2))
