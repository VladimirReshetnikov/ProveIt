#!/usr/bin/env python3
"""Pinned graph delta and source signature checks; no Lean is executed."""
from pathlib import Path
import hashlib,json,random,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
 raise SystemExit('Run with python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={
 'wshift':(P/'Natural79WShift.lean','7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1'),
 'g79':(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'),
 'g80':(D/'research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'),
 'lean79':(D/'research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36'),
 'lean80':(D/'research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean','015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9'),
 'model':(D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')}
s={}
for name,(path,expected) in pins.items():
 data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==expected,name;s[name]=data.decode()
a,b=json.loads(s['g79']),json.loads(s['g80'])
assert a['domain']==b['domain']=='nonnegative integers'
assert a['witnesses']==b['witnesses'] and a['witnesses'][6]=='n_w'
assert a['fixed_numerals']==b['fixed_numerals'] and a['output']==b['output']=='out'
assert len(a['source'])==a['operations']==79 and len(b['source'])==b['operations']==80
assert ['w','+','n_w',1] in b['source']
expected=[[n,op,'n_w' if x=='w' else x,'n_w' if y=='w' else y]
          for n,op,x,y in b['source'] if n!='w']
assert a['source']==expected
# Independently compare each literal Lean block with its pinned JSON graph.
pattern=re.compile(r'^  let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)$')
def atom(x):return int(x) if x.isdecimal() else x
for graph,name in ((a,'lean79'),(b,'lean80')):
 source=s[name];lo='  -- BEGIN LITERAL GRAPH\n';hi='  -- END LITERAL GRAPH\n'
 assert source.count(lo)==source.count(hi)==1
 rows=[]
 for line in source.split(lo,1)[1].split(hi,1)[0].splitlines():
  match=pattern.fullmatch(line);assert match,line
  n,x,op,y=match.groups();rows.append([n,op,atom(x),atom(y)])
 assert rows==graph['source']
 assert re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.var (\d+)$',source,re.M)==[(n,str(i)) for i,n in enumerate(graph['witnesses'])]
 assert re.findall(r'^  let (\w+) : Expr \(Fin 14\) := \.constant \(p (\d+)\)$',source,re.M)==[(n,str(i)) for i,n in enumerate(graph['fixed_numerals'])]
 assert '  ⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in source
# Finite signed controls supplement the exact rowwise identity.
mod=1000003; rng=random.Random(79796)
def evaluate(graph,values):
 env=values.copy()
 for n,op,x,y in graph['source']:
  x=x if type(x) is int else env[x];y=y if type(y) is int else env[y]
  env[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%mod
 return env['out']
for _ in range(300):
 val={n:rng.randrange(-100,101) for n in a['witnesses']+a['fixed_numerals']}
 parent=val.copy();parent['n_w']-=1
 assert evaluate(a,val)==evaluate(b,parent)
source=s['wshift']
for token in ('def down80','if j = 6 then v j - 1 else v j','theorem output_eval',
 'v79 6 = v80 6 + 1','∀ j, j ≠ 6 → v79 j = v80 j','theorem internalZero_iff_related',
 'theorem exists_zero_iff_of_positive','(positive_w : ∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6)',
 'exists_add_of_le','simpa [w, add_comm] using hz','(internalZero_iff_related p hw).mp hv',
 '(internalZero_iff_related p (related_lift w)).mpr hw'):
 assert token in source,token
for n in ('output_eval','internalZero_iff_related','exists_zero_iff_of_positive'):
 assert f'#print axioms DiophantineConsistency.Natural79WShiftDraft.{n}' in source
assert 'theorem internalZero_iff' in s['model']
print(json.dumps({'scope':'pinned literal graph correspondence and source-shape checks; no Lean or model theorem',
 'pinned_files':len(pins),'graph_rows':[79,80],'deleted_shift':'w=n_w+1','signed_controls_modular':300,
 'positive_w_explicitly_assumed':True,'axiom_reports_not_run':3},sort_keys=True,indent=2))
