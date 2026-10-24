import json,pathlib,random
p=pathlib.Path(__file__).resolve().parent;x=json.loads((p/'p11_degree277.json').read_text());s=x['source'];deps={a:[v for v in (b,c) if isinstance(v,str)] for a,o,b,c in s};live=set();todo=[x['output']]
while todo:
 a=todo.pop()
 if a in live:continue
 live.add(a);todo.extend(deps.get(a,[]))
if len(s)!=111 or any(a not in live for a,*_ in s):raise RuntimeError('liveness')
r=random.Random(711)
for _ in range(200):
 e={k:r.randrange(1,9) for k in x['witnesses']+x['fixed_numerals']}
 for a,o,b,c in s:
  b=e[b] if isinstance(b,str) else b;c=e[c] if isinstance(c,str) else c;e[a]=b+c if o=='+' else b-c if o=='-' else b*c
 if e['I']!=e['i']*e['c']**2:raise RuntimeError('I')
 d=e['delta'];z=e['Zbar'];A=e['A'];B=e['Bf'];C=e['Cnum']
 center=d*d*((z*z-A-B)**2-4*A*B)-2*d*C*(z*z+A+B)+C*C
 if e['N8']!=center*center-64*d**3*A*B*C*z*z:raise RuntimeError('norm')
print('PASS:111 live operations;200 independent norm identities')
