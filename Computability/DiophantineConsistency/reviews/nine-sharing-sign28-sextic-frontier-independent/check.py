#!/usr/bin/env python3
"""Independent per-node substitution and coefficient-binding audit; no Lean."""
import hashlib,gzip,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-sextic-candidate';O=D/'research/nine-sharing-sign31-sextic-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'build.py':'376b84ca8aa200ba6f4fccf8586539774b44d2cdb417488172c36c4c3df5a4dc','check.py':'2eaa625e76ca9e34d9253fa42223efdbc149f99b7996f198e82ea034563a6daa','seed.json':'b5ea881fefc64c14dafa59c8639a0786224e81b75bb2517eccb1e0021fbb10aa','result.json':'6220007f2309e1467f2a2175631fe62bca9eba142e0c0ceed3a7c95e752fdd23'}.items():assert sha(P/n)==h
assert sha(O)=='827740a7f65961bd1a04ae424f4c8873a636285d2b1410bb72d0bee7e3e9e6c1'
a=json.loads(O.read_bytes());b=json.loads((P/'seed.json').read_bytes());assert (P/b['source']).resolve()==O and b['source_sha256']==sha(O) and b['fixed_ports']==a['fixed_ports'] and b['coefficient_binding']==a['coefficient_binding']
assert (a['witness_count'],len(a['residuals']))==(31,22) and (b['witness_count'],b['total_coordinates'],b['distinguished_input_coordinate'],len(b['residuals']))==(28,29,0,19)
def variables(t):
 if t[0]=='var':return {t[1]}
 if t[0] in ('num','port'):return set()
 assert t[0] in ('add','sub','mul') and len(t)==3
 return variables(t[1])|variables(t[2])
def nonnegative(t):
 if t[0]=='var':return isinstance(t[1],int)
 if t[0]=='num':return type(t[1])==int and t[1]>=0
 if t[0]=='port':return t[1] in b['coefficient_binding']['ports']
 return t[0] in ('add','mul') and nonnegative(t[1]) and nonnegative(t[2])
def map_tree(t,k,r):
 if t[0]=='var':
  if t[1]==k:return map_tree(r,k,None)
  assert 0<=t[1]<=current
  return ['var',t[1]-(t[1]>k)]
 if t[0] in ('num','port'):return t[:]
 return [t[0],map_tree(t[1],k,r),map_tree(t[2],k,r)]
rows=a['residuals'];affected=[];current=31
for step,(gate,k) in zip(b['elimination_steps'],[('X',16),('c2',22),('normalized_S2',28)]):
 assert step['gate']==gate and step['old_coordinate_at_step']==k
 x=[r for r in rows if r['gate']==gate];assert len(x)==1
 z=x[0];assert z['kind']=='positive' and z['expr'][0:2]==['sub',['var',k]]
 rhs=z['expr'][2];assert rhs==step['replacement_before_drop'] and k not in variables(rhs) and 0 not in variables(rhs) and all(0<=v<=current for v in variables(rhs)) and nonnegative(rhs)
 affected.append((gate,[r['gate'] for r in rows if k in variables(r['expr'])]))
 rows=[dict(r,expr=map_tree(r['expr'],k,rhs)) for r in rows if r['gate']!=gate];current-=1
assert rows==b['residuals']
def deg(t):
 if t[0]=='var':return 1
 if t[0] in ('num','port'):return 0
 return deg(t[1])+deg(t[2]) if t[0]=='mul' else max(deg(t[1]),deg(t[2]))
degrees={r['gate']:deg(r['expr']) for r in rows};assert max(degrees.values())==3 and set.union(*(variables(r['expr']) for r in rows))==set(range(1,29))
# First row unchanged; independently checked q3 in the 31-seed audit has x1^3 coefficient -beta^3.
assert rows[0]==a['residuals'][0] and rows[0]['gate']=='q3'
bind=b['coefficient_binding']
for k in ('certificate','ordinary_proof'):assert sha((P/bind[k]).resolve())==bind[k+'_sha256']
for k,m in bind['ports'].items():
 data=((P/bind['path']/m['file']).resolve()).read_bytes();raw=gzip.decompress(data);v=int.from_bytes(raw,'big');assert hashlib.sha256(data).hexdigest()==m['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'] and v.bit_length()==m['bits'] and v>0
prior=D/'reviews/nine-sharing-sign31-sextic-frontier-independent/check.py';assert sha(prior)=='d4be4a4d528a4ee167ac546e416d11a2830298a25fa1c85852884e90bd0d40f4';subprocess.run([sys.executable,'-I','-S','-B',str(prior)],check=True,capture_output=True,timeout=30)
for script,args in [('build.py',['--check']),('check.py',[])]:
 x=subprocess.run([sys.executable,'-I','-S','-B',str(P/script),*args],capture_output=True,check=True,timeout=30);assert not x.stderr
 if script=='check.py':assert x.stdout==(P/'result.json').read_bytes()
print(json.dumps({'status':'PASS_SOURCE_ONLY','steps':affected,'witnesses':28,'residuals':19,'max_residual_degree':3,'exact_degree':'6; unchanged q3 has x1^3 coefficient -beta^3, beta > 0, hence x1^6 coefficient >= beta^6','scope':'external AST and conditional mathematical lift/drop; no Lean bridge, endpoint or quartic Jones application'},indent=2,sort_keys=True))
