#!/usr/bin/env python3
"""Check graph-specific guard cut and source interfaces; no Lean run."""
from pathlib import Path
import hashlib,json,re,random,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={
 'client':(P/'Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a'),
 'units':(D/'research/ordinary14-natural79-factor-residues-draft/Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d'),
 'graph_source':(D/'research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36'),
 'graph':(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'),
 'model':(D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')}
s={}
for n,(p,h) in pins.items():
 data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==h,n;s[n]=data.decode()
graph=json.loads(s['graph']);assert graph['operations']==len(graph['source'])==79
assert graph['witnesses'][0]=='n_J' and graph['witnesses'][6]=='n_w'
pat=re.compile(r'^  let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)$')
def atom(x):return int(x) if x.isdecimal() else x
lo='  -- BEGIN LITERAL GRAPH\n';hi='  -- END LITERAL GRAPH\n';src=s['graph_source']
rows=[]
for line in src.split(lo,1)[1].split(hi,1)[0].splitlines():
 m=pat.fullmatch(line);assert m,line;n,x,op,y=m.groups();rows.append([n,op,atom(x),atom(y)])
assert rows==graph['source']
assert re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$',src,re.M)==[(n,str(i)) for i,n in enumerate(graph['witnesses'])]
assert re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$',src,re.M)==[(n,str(i)) for i,n in enumerate(graph['fixed_numerals'])]
assert '  ⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in src
# Evaluate exactly the guard dependency DAG as sparse formal polynomials,
# specializing n_J=n_w=0. No finite sampling establishes this identity.
needed={'guard'}
for n,op,x,y in reversed(rows):
 if n in needed:needed.update(z for z in (x,y) if isinstance(z,str))
def add(a,b):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 out={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(sorted(ka+kb));out[k]=out.get(k,0)+va*vb
 return {k:v for k,v in out.items() if v}
def const(n):return {():n} if n else {}
formal={n:({} if n in ('n_J','n_w') else {(n,):1}) for n in graph['witnesses']+graph['fixed_numerals']}
for n,op,x,y in rows:
 if n not in needed:continue
 x=const(x) if type(x) is int else formal[x];y=const(y) if type(y) is int else formal[y]
 formal[n]=add(x,y) if op=='+' else add(x,neg(y)) if op=='-' else mul(x,y)
f=formal['n_F'];alpha=formal['n_alpha'];k=formal['K0']
expected=add(neg(mul(add(add(f,alpha),const(1)),k)),neg(f))
assert formal['guard']==expected
# Nonnegative controls include zero K0, where strict negativity would be false.
rng=random.Random(7900)
for _ in range(300):
 F,A,K=(rng.randrange(100) for _ in range(3));guard=-(F+A+1)*K-F
 assert guard<=0
assert -(0+0+1)*0-0==0
client=s['client'];units=s['units']
for token in ('theorem eval_one_of_pair_unit','theorem guard_zero_cut','(hK : (p 1 : DiffRing V)=ι K)',
 '(hJ : v 0=0) (hw : v 6=0)','theorem J_pos_of_zero_w_zero',
 '(hz : InternalZero (P79NaturalForcedW.graph p).output v) (hw : v 6=0)',
 'Natural79ConcreteUnitsDraft.units_of_zero_w_zero p v hz hw',
 'units.2.2.2.1','ι_nonneg K'):
 assert token in client,token
assert 'theorem units_of_zero_w_zero' in units
assert '(pairEval (P79NaturalForcedW.graph p).guardFactor v).2+1 ∧' in units
for name in ('guard_zero_cut','J_pos_of_zero_w_zero'):
 assert f'#print axioms DiophantineConsistency.Natural79ZeroWJPosDraft.{name}' in client
assert 'theorem ι_nonneg' in s['model']
print(json.dumps({'scope':'graph-cut and selected source interfaces; no Lean elaboration or iPRA theorem',
 'pinned_files':len(pins),'graph_rows_checked':len(rows),'exact_guard_polynomial_cut':True,
 'finite_nonnegative_controls':300,'zero_K0_control':True,'axiom_commands_unexecuted':2},sort_keys=True,indent=2))
