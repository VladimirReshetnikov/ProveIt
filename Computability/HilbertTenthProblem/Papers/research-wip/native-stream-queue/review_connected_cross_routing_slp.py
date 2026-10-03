#!/usr/bin/env python3
"""Independent complete-polynomial/cost audit of the connected SLP prototype."""
import argparse,copy,hashlib,importlib.util,itertools,json,os,py_compile,random,sys,tempfile
from pathlib import Path
SOURCE_HASH='3dd949eae682c7b57d2c3ee9f8e86dad5d40c156a33d6010568868bc1b9173e4'
HELPER_HASH='91aa4fedbf1251baa2b385065f97dbe79c59cbce04244839c753558b55c67a4e'

def check(ok,msg):
 if not ok:raise AssertionError(msg)

def load(path):
 path=Path(path);name='_independent_connected_helper';spec=importlib.util.spec_from_file_location(name,path);mod=importlib.util.module_from_spec(spec);prior=sys.modules.get(name);sys.modules[name]=mod
 try:exec(compile(path.read_bytes(),str(path),'exec'),mod.__dict__)
 finally:
  if prior is None:sys.modules.pop(name,None)
  else:sys.modules[name]=prior
 return mod

def polyadd(a,b,sign=1):
 out=a.copy()
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}

def polymul(a,b):
 out={}
 for i,x in a.items():
  for j,y in b.items():
   ij=tuple(sorted(i+j));out[ij]=out.get(ij,0)+x*y
 return {k:v for k,v in out.items() if v}

def affine(xs=(),constant=0):
 row={'':constant} if constant else {}
 for x,c in xs:row[x]=row.get(x,0)+c
 return {x:c for x,c in row.items() if c}

def manual(desc,T,m):
 d=desc['dimension'];ins=desc['instructions'];halt=next(i for i,z in enumerate(ins) if z['op']=='HALT');branches=[]
 for q,z in enumerate(ins):
  if z['op']=='INC':branches.append((q,z['target'],z['counter'],'inc'))
  if z['op']=='TEST':branches.extend([(q,z['target'],z['counter'],'zero'),(q,z['positive'],z['counter'],'positive')])
 R=len(branches);base=max(2,R+1);rows=[];variables=[];cross=[]
 for t in range(T+1):variables.extend([f'q{t}',f'h{t}']+[f'c{t}_{j}' for j in range(d)])
 for t in range(T):
  for k,(_,_,_,kind) in enumerate(branches,1):
   variables += [f'b{t}_{k}']+[f'a{t}_{k}_{j}' for j in range(d)]
   if kind=='positive':variables.append(f's{t}_{k}')
 variables += [f'u{i}' for i in range(T+1)]+['charge'];params=[f'x{j}' for j in range(d)]
 rows += [affine([('q0',1)],-desc['start']),affine([('h0',1)],-1)]
 rows += [affine([(f'c0_{j}',1),(f'x{j}',-1)]) for j in range(d)];rows.append(affine([(f'q{T}',1)],-halt))
 for t in range(T):
  rows.append(affine([(f'b{t}_{k}',1) for k in range(1,R+1)],-1))
  rows.append(affine([(f'q{t}',1)]+[(f'b{t}_{k}',-z[0]) for k,z in enumerate(branches,1)]))
  rows.append(affine([(f'q{t+1}',1)]+[(f'b{t}_{k}',-z[1]) for k,z in enumerate(branches,1)]))
  for j in range(d):
   rows.append(affine([(f'c{t}_{j}',1)]+[(f'a{t}_{k}_{j}',-1) for k in range(1,R+1)]))
   delta=[(f'b{t}_{k}',(-1 if kind=='inc' else 1 if kind=='positive' else 0) if counter==j else 0) for k,(_,_,counter,kind) in enumerate(branches,1)]
   rows.append(affine([(f'c{t+1}_{j}',1),(f'c{t}_{j}',-1)]+delta))
  rows.append(affine([(f'h{t+1}',1),(f'h{t}',-base)]+[(f'b{t}_{k}',-k) for k in range(1,R+1)]))
  for k,(_,_,counter,kind) in enumerate(branches,1):
   if kind=='zero':rows.append(affine([(f'a{t}_{k}_{counter}',1)]))
   if kind=='positive':rows.append(affine([(f'a{t}_{k}_{counter}',1),(f'b{t}_{k}',-1),(f's{t}_{k}',-1)]))
   for other in range(1,R+1):
    if other!=k:cross += [(f'b{t}_{other}',f'a{t}_{k}_{j}') for j in range(d)]
 for t in range(T+1):
  rr=[(f'u{t}',m)]
  if t:rr.append((f'u{t-1}',-1))
  if t<T:rr.append((f'u{t+1}',-1))
  if t==0:rr.append(('charge',-1))
  rows.append(affine(rr))
 rows.append(affine([(f'u{T}',1)],-1))
 p={}
 for row in rows:
  a={((x,) if x else ()):v for x,v in row.items()};p=polyadd(p,polymul(a,a))
 for a,b in cross:p=polyadd(p,{tuple(sorted((a,b))):1})
 return variables,params,rows,cross,p,R

def expand_slp(packet):
 env={x:{(x,):1} for x in packet['variables']+packet['parameters']};available=set(env);ops={'add':0,'sub':0,'mul':0};keys=set();polys={}
 def value(x):return {():x} if type(x) is int and x else {} if type(x) is int else env[x]
 for g in packet['gates']:
  name,op,a,b=(g[k] for k in ('name','op','left','right'))
  check(type(name)is str and name not in available,'unique gate');check(op in ops,'valid operation')
  check(all(type(x)is int or type(x)is str and x in available for x in (a,b)),'closed acyclic gate')
  key=(op,a,b);check(key not in keys,'structural CSE duplicate');keys.add(key)
  env[name]=polymul(value(a),value(b)) if op=='mul' else polyadd(value(a),value(b),1 if op=='add' else -1)
  check(max(map(len,env[name]),default=0)<=2,'quadratic source intermediate')
  ops[op]+=1;available.add(name);polys[name]=env[name]
 live={packet['output']} if type(packet['output']) is str else set()
 for g in reversed(packet['gates']):
  if g['name'] in live:
   for x in (g['left'],g['right']):
    if type(x)is str:live.add(x)
 check(all(g['name'] in live for g in packet['gates']),'unused paid gate')
 return value(packet['output']),value,ops

def run(helper,source):
 check(hashlib.sha256(Path(helper).read_bytes()).hexdigest()==HELPER_HASH,'helper pin')
 check(hashlib.sha256(Path(source).read_bytes()).hexdigest()==SOURCE_HASH,'source pin');h=load(helper)
 shapes=[]
 for d,R in [(1,0),(1,1),(1,2),(2,2),(2,3),(3,4),(6,4),(2,5),(4,8)]:
  if R==0:ins=[dict(op='HALT',counter=0,target=0,positive=0)]
  else:ins=[dict(op='INC',counter=k%d,target=(k+1)%(R+1),positive=0) for k in range(R)]+[dict(op='HALT',counter=0,target=0,positive=0)]
  shapes.append(({'dimension':d,'start':0,'instructions':ins},[0,1,3]))
 for d,ins in [(1,[('TEST',0,1,0),('HALT',0,0,0)]),(2,[('TEST',0,2,1),('INC',1,0,0),('HALT',0,0,0)])]:
  shapes.append(({'dimension':d,'start':0,'instructions':[dict(zip(('op','counter','target','positive'),z)) for z in ins]},[0,1,3,7]))
 for d,ins,start,horizons in [
  (3,[('TEST',0,3,1),('INC',1,2,0),('TEST',2,0,1),('HALT',0,0,0)],1,[1,4]),
  (2,[('TEST',j%2,4,(j+1)%4) for j in range(4)]+[('HALT',0,0,0)],0,[1,3]),
  (6,[('TEST',2,2,1),('TEST',5,2,0),('HALT',0,0,0)],0,[1,3])]:
  shapes.append(({'dimension':d,'start':start,'instructions':[dict(zip(('op','counter','target','positive'),z)) for z in ins]},horizons))
 counts={'forms':0,'literal_rows':0,'gates':0,'complete_polynomial_identities':0,'full_tuple_evaluations':0,'guards':0,'copies':0};records=[];rng=random.Random(84021)
 for desc,horizons in shapes:
  for T in horizons:
   m=3 if T==0 else 5;vs,ps,rows,cross,expected,R=manual(desc,T,m);ledgers={}
   for mode in ('direct','column_diagonal','row_diagonal','row_complement'):
    p=h.build(source,desc,T,m,mode);check(p['variables']==vs and p['parameters']==ps,'complete interface');check(p['linear_rows']==rows,'manual residual list');check(p['direct_cross_terms']==[list(z) for z in cross],'manual cross list');actual,val,ops=expand_slp(p)
    check(actual==expected,'complete exact polynomial');check(max(map(len,actual),default=0)==2,'exact degree two');counts['complete_polynomial_identities']+=1
    for row,register in zip(rows,p['residual_registers']):check(val(register)=={((x,) if x else ()):v for x,v in row.items()},'each affine residual');counts['literal_rows']+=1
    ledger={'multiplications':ops['mul'],'additions_subtractions':ops['add']+ops['sub'],'total':sum(ops.values())};check(all(p['counts'][k]==v for k,v in ledger.items()),'literal gate count');counts['gates']+=sum(ops.values());counts['forms']+=1;ledgers[mode]=ledger
    for signed in (False,True):
     assignment={x:rng.randrange(-3 if signed else 0,5) for x in vs+ps}
     direct=sum(sum(c*(assignment[x] if x else 1) for x,c in row.items())**2 for row in rows)+sum(assignment[x]*assignment[y] for x,y in cross)
     check(h.evaluate(source,p,assignment,natural=not signed)==direct,'manual full evaluation');counts['full_tuple_evaluations']+=1
   records.append({'d':desc['dimension'],'R':R,'T':T,'m':m,'ledgers':ledgers})
 desc=shapes[-1][0];p=h.build(source,desc,3);assignment=dict.fromkeys(p['variables']+p['parameters'],1)
 def reject(f):
  try:f()
  except (ValueError,TypeError):counts['guards']+=1
  else:raise AssertionError('bad call accepted')
 for val in (True,1.0,'1',None):
  reject(lambda val=val:h.build(source,desc,val));reject(lambda val=val:h.build(source,desc,1,m=val))
 for key in ('variables','parameters','gates','residual_registers'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:h.checked(source,q))
 for i in [0,len(p['gates'])//2,len(p['gates'])-1]:
  for key in ('left','right'):
   q=copy.deepcopy(p);old=q['gates'][i][key];q['gates'][i][key]=float(old) if type(old)is int else 0.0;reject(lambda q=q:h.checked(source,q))
 for key in ('total','multiplications','additions_subtractions'):
  q=copy.deepcopy(p);q['counts'][key]=float(q['counts'][key]);reject(lambda q=q:h.checked(source,q))
 for key in ('horizon','m'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:h.checked(source,q))
 for val in (True,1.0,-1):
  a=assignment.copy();a[next(iter(a))]=val;reject(lambda a=a:h.evaluate(source,p,a))
 for val in (1,0,None):reject(lambda val=val:h.evaluate(source,p,assignment,natural=val))
 for q in [h.build(source,desc,3),h.checked(source,p)]:
  q['gates'][0]['left']='poison';q['linear_rows'][0].clear();q['program']['instructions'].clear();check(h.checked(source,p)==p,'defensive access');counts['copies']+=1
 # A forged timestamp/size bytecode cache must not defeat source-byte authentication.
 original=Path(source).read_bytes()
 with tempfile.TemporaryDirectory(prefix='independent_connected_pyc_') as td:
  f=Path(td)/'substrate.py';prefix=b'raise RuntimeError("FORGED_BYTECODE_EXECUTED")\n#';f.write_bytes(prefix+b'x'*(len(original)-len(prefix)));stamp=f.stat().st_mtime_ns
  py_compile.compile(str(f),doraise=True,invalidation_mode=py_compile.PycInvalidationMode.TIMESTAMP);f.write_bytes(original);os.utime(f,ns=(stamp,stamp))
  check(h.build(f,desc,3)==p,'forged bytecode isolation');counts['forged_bytecode_rejections']=1
 return {'status':'PASS','helper_sha256':HELPER_HASH,'source_sha256':SOURCE_HASH,'counts':counts,'complete_ledgers':records,'scope':'Exact complete polynomial on all integer tuples; natural-zero semantics and externally fixed horizon inherited. Network coercivity requires m>=5; m=3 only a finite polynomial recurrence option.'}

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--helper',type=Path,required=True);a.add_argument('--source',type=Path,required=True);a.add_argument('--receipt',type=Path,default=Path(__file__).with_suffix('.json'));a.add_argument('--write',action='store_true');args=a.parse_args();result=run(args.helper,args.source)
 if args.write:args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:check(json.dumps(json.loads(args.receipt.read_text()),sort_keys=True)==json.dumps(result,sort_keys=True),'exact saved receipt')
 print(json.dumps({'status':'PASS','counts':result['counts']},sort_keys=True))
