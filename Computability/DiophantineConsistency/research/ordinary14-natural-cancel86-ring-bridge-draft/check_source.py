#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'RingNatural86To74.lean').read_text();m=(P/'Natural86Model.lean').read_text()
for t in ('theorem qF_cut','theorem guard_cut','theorem restricted_eval','theorem guard_eval','theorem output_eval','theorem positiveShift_eval','theorem output_eq_positiveShift'):
 assert t in s,t
for t in ('ModelDifferenceRing.internalZero_iff','RingNatural86To74Draft.output_eq_positiveShift'):
 assert t in m,t
p=json.loads((D/'research/ordinary14-positive-guard74/candidate.json').read_text());g=json.loads((D/'research/ordinary14-root74-natural-cancel86/candidate.json').read_text())
def calc(graph,env):
 e=env.copy()
 for n,op,x,y in graph['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
rng=random.Random(860074)
for mod in (4,12,17):
 for _ in range(200):
  env={v:rng.randrange(-6,7) for v in g['witnesses']+g['fixed_numerals']}
  shifted={x:env['n_'+x]+1 for x in p['witnesses']};shifted.update({x:env[x] for x in p['fixed_numerals']})
  a=calc(g,env);b=calc(p,shifted)
  for n in ('F0','F1','Fa','Fs','guard','out'):assert a[n]%mod==b[n]%mod,(mod,n)
A=D/'research/ordinary14-natural-cancel86-lean-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'make_graph.py'),'--check'],cwd=D,capture_output=True,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
paths=[P/'RingNatural86To74.lean',P/'Natural86Model.lean',A/'P86NaturalCancel.lean',D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean',D/'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean',D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean']
print(json.dumps({'scope':'source interface, generator replay and finite ring controls; no Lean or physical binding','ring_controls':600,'files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
