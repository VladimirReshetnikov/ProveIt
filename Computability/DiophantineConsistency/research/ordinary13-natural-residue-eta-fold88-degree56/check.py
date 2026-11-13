#!/usr/bin/env python3
"""Pin local rewrite, exact polynomial identities, liveness and inherited ray."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(x):return hashlib.sha256(x).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(str(p),sha(b));return b
raw=pin(D/'research/ordinary13-natural-residue-forced89-degree56/candidate.json','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a');p=json.loads(raw)
c=json.loads(pin(P/'candidate.json','f71cb18bdc28088a7a7c7c7ae84afc15e49470ee3d4fa4076d8c25d6d2b89b58'));assert c['parent_sha256']==sha(raw)
assert c['domain']==p['domain'] and c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals'] and c['output']==p['output']
expect=[]
for r in p['source']:
 if r[0] in {'shift_zeta','g52'}:continue
 if r[0]=='k':expect.extend([['kbase','+','shift_eta','n_zeta'],['k','+','kbase',1]])
 elif r[0]=='r0':expect.append(['r0','-','kbase','R'])
 else:expect.append(r)
assert c['source']==expect and len(expect)==c['operations']==88
rows={r[0]:r for r in p['source']}
assert rows['shift_zeta']==['shift_zeta','+','n_zeta',1] and rows['k']==['k','+','shift_eta','shift_zeta']
assert rows['g52']==['g52','-','k','R'] and rows['r0']==['r0','-','g52',1]
assert [(n,o,a,b) for n,o,a,b in p['source'] if 'shift_zeta' in (a,b)]==[('k','+','shift_eta','shift_zeta')]
assert [(n,o,a,b) for n,o,a,b in p['source'] if 'g52' in (a,b)]==[('r0','-','g52',1)]
# Ring identities establish both replaced nodes exactly for arbitrary inputs.
def con(x):return {():x} if x else {}
def var(x):return {(x,):1}
def add(a,b,s=1):
 z=dict(a)
 for k,v in b.items():z[k]=z.get(k,0)+s*v
 return {k:v for k,v in z.items() if v}
e,z,R=map(var,['eta','zeta','R']);oldk=add(e,add(z,con(1)));newbase=add(e,z);newk=add(newbase,con(1))
assert oldk==newk and add(add(oldk,R,-1),con(1),-1)==add(newbase,R,-1)
known=set(c['witnesses']+c['fixed_numerals']);nodes={}
for n,o,a,b in expect:
 assert n not in known and o in ('+','-','*') and all(type(x) is int or x in known for x in (a,b)),n
 known.add(n);nodes[n]=(a,b)
seen={c['output']};todo=[c['output']]
while todo:
 for x in nodes.get(todo.pop(),()):
  if isinstance(x,str) and x not in seen:seen.add(x);todo.append(x)
assert set(nodes)|set(c['witnesses'])|set(c['fixed_numerals'])<=seen
# Re-run the parent's exact compact-port degree certificate and compare receipt.
run=subprocess.run([sys.executable,'-I','-S','-B',str(D/'research/ordinary13-natural-residue-forced89-degree56/check.py')],capture_output=True,check=True)
assert run.stdout==(D/'research/ordinary13-natural-residue-forced89-degree56/receipt.json').read_bytes()
receipt=json.loads(run.stdout);assert receipt['degree']==56 and receipt['operations']==88+1
print(json.dumps({'scope':'exact all-port k/r0 ring identities, unchanged downstream DAG and inherited compact-port degree; no Lean','variables':13,'operations':88,'degree':56,'output_polynomial_identical_for_all_ports_and_inputs':True,'counts':dict(sorted(Counter(r[1] for r in expect).items())),'inherited_compact_ray_coefficient':receipt['ray_leading_coefficient'],'parent_checker_reproduces':True,'lean_elaboration':False},sort_keys=True,indent=2))
