import json,pathlib,random,collections
p=pathlib.Path(__file__).resolve().parent;x=json.loads((p/'p12_degree78.json').read_text());s=x['source'];names=set(x['witnesses']+x['fixed_numerals']);deps={}
for dst,op,a,b in s:
 if not all(isinstance(v,int) or v in names for v in (a,b)):raise RuntimeError('topology')
 if dst in names:raise RuntimeError('duplicate')
 names.add(dst);deps[dst]=[v for v in (a,b) if isinstance(v,str)]
live=set();todo=[x['output']]
while todo:
 a=todo.pop()
 if a in live:continue
 live.add(a);todo.extend(deps.get(a,[]))
if len(s)!=101 or any(a not in live for a,*_ in s):raise RuntimeError('count')
rng=random.Random(871)
for _ in range(200):
 e={k:rng.randrange(1,12) for k in x['witnesses']+x['fixed_numerals']}
 for dst,op,a,b in s:
  a=e[a] if isinstance(a,str) else a;b=e[b] if isinstance(b,str) else b
  e[dst]=a+b if op=='+' else a-b if op=='-' else a*b
 q=e['q'];U=q*q*e['Y'];D=U*(e['X']+e['a']*e['c'])+e['H']*(U*e['gamma']+q*e['X']*e['Y']-(e['k']-e['R']-1))
 if e['A1']!=D*D-U*U*(1+e['Delta']*e['c']**2):raise RuntimeError('carrier')
 if e['P12']!=(1+e['A0'])*(1+e['A1'])*(1+e['N'])-1:raise RuntimeError('finalizer')
print('PASS:101 live operations;200 independent carrier/finalizer checks')
