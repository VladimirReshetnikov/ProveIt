#!/usr/bin/env python3
import hashlib,json,gzip,random,sys,subprocess
from pathlib import Path
from itertools import product
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
root=Path(__file__).resolve().parents[2]; pkg=root/'research/current14-carrier65-local-rewrite-search';gpath=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';engine=root/'research/p64-qcube79-local-rewrite-search/search.py';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(gpath)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(engine)=='4c8e09ecb5ca438123ab0ac1b6cb6e07b5d27f95c6cee651debde2ccbb438f46' and sha(pkg/'search.py')=='49db36fed16a480b785067ac59109b07bda2cfc01f601c266627140baa5dcd8e'
r=json.loads((pkg/'result.json').read_text());g=json.loads(gpath.read_text());rows=g['source'];out=g['output'];variables=g['witnesses']+g['fixed_numerals'];assert len(rows)==65 and len(g['witnesses'])==14 and set(g['fixed_numerals'])==set(g['coefficient_binding']['ports'])=={'K0','MC','MF','beta'}
P=1000000007;N=3;seed=0x46be
assert all(P%d for d in range(2,int(P**.5)+1)) and P%4==3
def op(o,a,b):return tuple((x+y if o=='+' else x-y if o=='-' else x*y)%P for x,y in zip(a,b))
def live(rs,output):
 deps={n:(a,b) for n,_,a,b in rs}; seen=set(); todo=[output]
 while todo:
  n=todo.pop()
  if n in deps and n not in seen:seen.add(n);todo.extend(deps[n])
 return len(seen)
assert live(rows,out)==65
ports={}
for n,m in g['coefficient_binding']['ports'].items():
 b=(gpath.parent/'coefficients'/m['file']).read_bytes();assert hashlib.sha256(b).hexdigest()==m['gzip_sha256'];raw=gzip.decompress(b);assert hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'];ports[n]=int.from_bytes(raw,'big')%P
assert ports==r['fixed_port_residues']
def independent(fixed):
 rng=random.Random(seed); vals={x:tuple(rng.randrange(1,P) for _ in range(N)) for x in variables};vals.update({k:(v,)*N for k,v in fixed.items()});vals.update({i:(i,)*N for i in range(5)})
 found=[];aliases=[];signs=[];first=queries=sq=nonconstzero=targetzero=0
 consumers={n:[] for n,_,_,_ in rows}
 for dest,o,a,b in rows:
  for n in {a,b}:
   if n in consumers:consumers[n].append((o,a,b))
 for idx,(name,o,a,b) in enumerate(rows):
  assert name not in vals and a in vals and b in vals
  target=op(o,vals[a],vals[b]);keys=list(vals);targetzero+=any(x==0 for x in target);pool={}
  def add(tup,desc):pool.setdefault(tup,[]).append(desc)
  for i,x in enumerate(keys):
   for y in keys[i:]:
    for typ in ('+','*'):add(op(typ,vals[x],vals[y]),(typ,x,y));first+=1
   for y in keys:add(op('-',vals[x],vals[y]),('-',x,y));first+=1
  for typ,x,y in pool.get(target,[]):
   if live(rows[:idx]+[[name,typ,x,y]]+rows[idx+1:],out)<65:found.append(('one',name,typ,x,y))
  for x in keys:
   if vals[x]==target:
    changed=[list(z) for z in rows if z[0]!=name]
    for z in changed:z[2:]=[x if v==name else v for v in z[2:]]
    if live(changed,x if name==out else out)<65:aliases.append((name,x))
  uses=consumers[name]
  if name!=out and uses and all(t=='*' and x==name and y==name for t,x,y in uses):
   want=tuple(-x%P for x in target)
   for x in keys:
    for y in keys:
     if op('-',vals[x],vals[y])==want and live(rows[:idx]+[[name,'-',x,y]]+rows[idx+1:],out)<65:signs.append((name,x,y))
  for c in keys:
   cv=vals[c]; needs=[('+',op('-',target,cv)),('-',op('+',target,cv)),('r-',op('-',cv,target))]
   if all(cv):needs.append(('*',tuple(t*pow(v,-1,P)%P for t,v in zip(target,cv))))
   elif c!=0:nonconstzero+=1
   for typ,need in needs:
    queries+=1
    for firstop,x,y in pool.get(need,[]):
     second=[name,'-',c,'__new__'] if typ=='r-' else [name,typ,'__new__',c]
     if live(rows[:idx]+[['__new__',firstop,x,y],second]+rows[idx+1:],out)<65:found.append(('two',name,firstop,x,y,typ,c))
  roots=[pow(t,(P+1)//4,P) for t in target]
  if all(x*x%P==t for x,t in zip(roots,target)):
   for sg in product((1,-1),repeat=N):
    sq+=1;need=tuple(x*y%P for x,y in zip(roots,sg))
    for typ,x,y in pool.get(need,[]):
     if live(rows[:idx]+[['__new__',typ,x,y],[name,'*','__new__','__new__']]+rows[idx+1:],out)<65:found.append(('square',name,typ,x,y))
  vals[name]=target
 return {'targets':len(rows),'targets_with_sample_zero':targetzero,'first_gates':first,'second_queries':queries,'sample_zero_nonconstant':nonconstzero,'square_root_queries':sq},found,aliases,signs
for key,fixed in [('result',{}),('fixed_port_result',ports)]:
 counts,found,aliases,signs=independent(fixed);assert counts==r[key]['counts'] and not found and not r[key]['one_gate_candidates'] and not r[key]['two_gate_candidates'] and not counts['targets_with_sample_zero'] and not counts['sample_zero_nonconstant']
 if not fixed:assert not aliases and not signs and r['extra']=={'aliases':[],'square_only_negations':[]}
assert r['positive_control']['aliases'] and any(x['target']=='b' and x['live']==3 for x in r['square_sign_control']['square_only_negations'])
run=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'search.py')],capture_output=True,text=True,check=True,timeout=180);assert not run.stderr and json.loads(run.stdout)==r
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'bounded target-equality one/two-gate replacements, uniform and fixed ports; aliases/square-sign uniform only; not global circuit minimality or Lean'},indent=2))
