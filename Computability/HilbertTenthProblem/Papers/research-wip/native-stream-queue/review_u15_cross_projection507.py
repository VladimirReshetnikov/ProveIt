"""Independent complete-source audit; source and saved parents pinned before import."""
import argparse,copy,hashlib,json,random,struct,tempfile,types,shutil
from collections import Counter
from pathlib import Path
import sympy as sp
if not __debug__:raise RuntimeError('Omit -O')
PIN='dc89cc030610a719b6f270ddfe9dbc5b75b1d7675bb9d13a223db160b23469a4'
PINS={
 'u15_packed_composed_units511.py':'234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38',
 'u15_unit_partition_frontier.py':'8e0514876e26b716e792dd7d8332c773fe15989eb558fc7e4fedff8046249ccf',
}
RECEIPT_PINS={'u15_packed_composed_units511.json':'68438604ba79c629bc7dc158860aeede5cc98108865f875562efda3fc352b667','u15_unit_partition_frontier.json':'3f3fd17dcb0f36f19b83f7aba7d3ebe081926c73786015d498540bf225bc6fc0'}
def need(v,s):
 if not v:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def pin(p,h):need(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==h,'Source pin '+p.name)
def load(p,name):
 m=types.ModuleType(name);m.__file__=str(p);exec(compile(p.read_bytes(),str(p),'exec'),m.__dict__);return m
def normalized(x):return json.loads(json.dumps(x))
def execute(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b;e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def at(e,v):return e[v] if type(v)is str else v

def polycut(rows,target,cuts):
 e={n:sp.Symbol(n) for n in cuts};d={n:(o,a,b) for n,o,a,b in rows}
 def get(n):
  if type(n)is int:return sp.Integer(n)
  if n in e:return e[n]
  need(n in d,'Unexpected cut input '+n);o,a,b=d[n];a,b=get(a),get(b);e[n]=a*b if o=='*' else a+b if o=='+' else a-b;return e[n]
 return sp.Poly(sp.expand(get(target)),*[e[n] for n in cuts])

CUTS={
 'v142':('v139','ZU','binary28','binary14','binary15'),
 'v156':('binary83',),
 'v175':('binary77','v32','v169','v170'),
 'v262':('binary77','v32','v169','v170','v167','binary75','v181','v193','v254'),
}
def literal_proof(a,b):
 local=[]
 for n,leaves in CUTS.items():
  p,q=polycut(a['source'],n,leaves),polycut(b['source'],n,leaves)
  z={v:sp.Symbol(v) for v in leaves}
  if n=='v142':wanted=z['v139']+2*(z['binary28']+z['binary14']-8)-z['ZU']
  elif n=='v156':wanted=z['binary83']+1
  elif n=='v175':wanted=z['binary77']*(z['v32']*z['v169']+z['v170'])
  else:wanted=z['binary77']*(z['v32']*z['v169']+z['v170'])+z['binary75']*(z['v167']*z['v169']*z['v181']+z['v193']*z['v254'])
  need(p==q and sp.expand(p.as_expr()-wanted)==0,'Independent literal identity '+n)
  local.append({'cut':n,'polynomial':str(p.as_expr())})
 # Independent expression interner, not the author's signature code. The
 # proof dependencies are checked before cuts replace their equal values.
 table={}
 def node(x):
  if x not in table:table[x]=len(table)
  return table[x]
 def evaluate(p):
  e={n:node(('input',n)) for n in p['parameters']+p['auxiliaries']}
  def get(x):return e[x] if type(x)is str else node(('constant',x))
  for n,o,x,y in p['polynomial_source']:
   xx,yy=get(x),get(y)
   if o in ('+','*'):xx,yy=sorted((xx,yy))
   e[n]=node(('cut',n)) if n in CUTS else node((o,xx,yy))
  return e,get
 x,gx=evaluate(a);y,gy=evaluate(b)
 for leaves in CUTS.values():
  for n in leaves:need(x[n]==y[n],'Cut atom changed '+n)
 need(a['comparisons']==b['comparisons'],'Comparison list changed')
 for v,w in a['comparisons']:need(gx(v)==gy(v) and gx(w)==gy(w),'Residual operand changed')
 need(x[a['output']]==y[b['output']],'Final polynomial DAG changed')
 for key in ('computed_loader_fields','tag_registers'):
  need(a[key]==b[key],key+' metadata changed')
  for v in a[key].values():need(gx(v)==gy(v),key+' value changed')
 for k,v in b['registers'].items():
  if k in a['registers']:need(gx(a['registers'][k])==gy(v),'Retained named value '+k)
 for f in a.get('unit_factors',[]):need(x[f['factor']]==y[f['factor']],'Norm/checksum factor changed')
 return {'local_identities':local,'comparison_operands':2*len(a['comparisons']),'complete_output_identity':True,'exact_DAG_nodes':len(table)}

def source_audit(p):
 names=p['parameters']+p['auxiliaries'];known=set(names);need(len(known)==len(names),'Duplicate inputs')
 for n,o,a,b in p['polynomial_source']:
  need(n not in known and o in ('+','-','*'),'Malformed gate')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Unbound gate');known.add(n)
 live={p['output']}
 for n,o,a,b in reversed(p['polynomial_source']):
  if n in live:live.update(v for v in (a,b) if type(v)is str)
 need(all(n in live for n,*_ in p['polynomial_source']),'Dead paid gate')
 for name,field in (('certificate','source'),('polynomial','polynomial_source')):
  rows=p[field];want={'operations':len(rows),'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows)}
  need(p['ledger'][name]==want,'Paid ledger mismatch')
 return live

def degree(p,prime=1009):
 def trim(x):
  while len(x)>1 and not x[-1]:x.pop()
  return x
 def add(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
 def mul(a,b):
  need(min(len(a),len(b))*(prime-1)**2<2**64,'Convolution carry')
  aa=int.from_bytes(struct.pack('<'+'Q'*len(a),*a),'little');bb=int.from_bytes(struct.pack('<'+'Q'*len(b),*b),'little');n=len(a)+len(b)-1
  return trim([v%prime for v in struct.unpack('<'+'Q'*n,(aa*bb).to_bytes(8*n,'little'))])
 e={n:[i+2] if n in p['fixed_parameters'] else [i%11,i%7+1] for i,n in enumerate(p['parameters']+p['auxiliaries'])}
 for n,o,a,b in p['polynomial_source']:
  a=e[a] if type(a)is str else [a%prime];b=e[b] if type(b)is str else [b%prime];e[n]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
 v=e[p['output']];return {'prime':prime,'exact_specialization_degree':len(v)-1,'nonzero_leader':v[-1]}

def run(source,root):
 pin(source,PIN)
 for n,h in PINS.items():pin(source.parent/n if (source.parent/n).is_file() else root/n,h)
 for n,h in RECEIPT_PINS.items():pin(root/n,h)
 raw=json.loads((root/'u15_packed_composed_units511.json').read_text())
 old={f"base:{int(f['ordinary'])}:{int(f['grouped'])}":f['compiler'] for f in raw['forms']}
 front=json.loads((root/'u15_unit_partition_frontier.json').read_text())['frontier_compilers']
 old.update({'frontier:'+str(i):f['compiler'] for i,f in enumerate(front)})
 m=load(source,'independent_cross507');rng=random.Random(5074513);records=[];counts=Counter()
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
  raise ValueError('Malformed accepted')
 for key,q in old.items():
  if key.startswith('base:'):
   _,o,g=key.split(':');p=m.build(bool(int(o)),grouped=bool(int(g)),root=root)
  else:p=m.build_frontier(int(key.split(':')[1]),root=root)
  need(normalized(m.canonical_parent(p,root=root))==q,'Saved actual parent mismatch')
  pjson=normalized(p);proof=literal_proof(q,pjson);counts['exact_local_identities']+=4;counts['complete_DAG_identities']+=1
  counts['exact_residual_identities']+=len(q['comparisons']);live=source_audit(pjson)
  need(pjson['polynomial_source'][len(pjson['source']):]==q['polynomial_source'][len(q['source']):],'Finalizer changed')
  for field in ('parameters','auxiliaries','fixed_parameters','rules','comparisons','output','unit_factors','unit_retained_comparison_map','unit_group_factors','unit_groups','group_anchor'):
   need(pjson.get(field)==q.get(field),'Current interface changed '+field)
  for k in ('positive_witnesses','equations'):need(pjson['ledger'][k]==q['ledger'][k],'Domain/count changed')
  for k,change in (('operations',4),('M',2),('A',2)):
   for part in ('certificate','polynomial'):need(q['ledger'][part][k]-pjson['ledger'][part][k]==change,'Saving mismatch')
  removed=set(r[0] for r in q['source'])-set(r[0] for r in pjson['source'])
  need(removed==set(pjson['cross_projection']['removed_registers']),'Removed rows mismatch')
  expected_aliases={k:v for k,v in q['registers'].items() if v in removed}
  need(pjson['proof_only_eliminated_registers']['registers']==expected_aliases,'Historical alias mismatch')
  need(all(v in live for v in pjson['registers'].values()),'Current alias points at dead source')
  need(set(expected_aliases)=={'W','Qdev','direction_mask','range_mask','Mc'},'Unexpected removed convenience aliases')
  for case in range(12):
   signed=case>=6;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   if not p['ordinary'] and not signed:v.update(L0=case%2,R0=(case//2)%2)
   a,b=execute(q['polynomial_source'],v),execute(pjson['polynomial_source'],v)
   ra=[at(a,x)-at(a,y) for x,y in q['comparisons']];rb=[at(b,x)-at(b,y) for x,y in pjson['comparisons']]
   need(ra==rb and a[q['output']]==b[pjson['output']],'Literal whole-source mismatch')
   need(m.evaluate(p,v,signed=signed,root=root)==b[pjson['output']],'Public evaluator mismatch')
   counts['complete_evaluations']+=1;counts['signed_cases']+=signed
  target=pjson['exact_degree_certificate']['exact_degree'];d=degree(pjson)
  need(d['exact_specialization_degree']==target and d['nonzero_leader'],'Exact degree not attained')
  counts['full_polynomial_degree_expansions']+=1
  v={n:1 for n in p['parameters']+p['auxiliaries']}
  for n in list(v)[::11]:
   for badvalue in (True,1.0,0,-1):
    if type(badvalue)is int and badvalue==0 and not p['ordinary'] and n in ('L0','R0'):continue
    vv=dict(v);vv[n]=badvalue;reject(lambda vv=vv:m.evaluate(p,vv,root=root))
  for field in ('registers','comparisons','cross_projection','exact_degree_certificate','cross_parent_form','ledger'):
   bad=copy.deepcopy(p);bad[field]=None;reject(lambda bad=bad:m.checked(bad,root=root))
  for badvalues in ({k:z for k,z in v.items() if k!=next(iter(v))},dict(v,unexpected=1)):
   reject(lambda badvalues=badvalues:m.evaluate(p,badvalues,root=root))
  changed=copy.deepcopy(p)
  j=next(j for j,row in enumerate(changed['polynomial_source']) if any(type(z)is int for z in row[2:]))
  row=list(changed['polynomial_source'][j]);k=next(k for k in (2,3) if type(row[k])is int);row[k]=float(row[k]);changed['polynomial_source'][j]=tuple(row)
  huge={n:10**100 for n in v};reject(lambda:m.evaluate(changed,huge,root=root))
  for fn in (lambda:m.canonical_parent(p,root=root),lambda:m.polynomial_source(p,root=root)):
   a=fn();a.clear();need(bool(fn()),'Returned object aliases cache');counts['copy_checks']+=1
  records.append({'form':key,'ledger':pjson['ledger'],'independent_proof':proof,'removed_registers':sorted(removed),'removed_convenience_aliases':expected_aliases,'degree':d})
 for bad in (0,1,0.0,None,'true'):
  reject(lambda bad=bad:m.build(bad,root=root));reject(lambda bad=bad:m.build(grouped=bad,root=root))
 for bad in (True,False,0.0,4,-1,None):reject(lambda bad=bad:m.build_frontier(bad,root=root))
 with tempfile.TemporaryDirectory(prefix='review-cross507-warm-') as tmp:
  tmp=Path(tmp);shutil.copyfile(source,tmp/source.name)
  for name in PINS:
   path=source.parent/name if (source.parent/name).is_file() else root/name
   shutil.copyfile(path,tmp/name)
  warm=load(tmp/source.name,'independent_cross507_warm');packet=warm.build(True,root=root)
  for name in PINS:
   path=tmp/name;data=path.read_bytes()
   try:
    path.write_bytes(data+b'\n# private source-pin test\n');reject(lambda:warm.build(True,root=root));counts['warm_source_pin_checks']+=1
   finally:path.write_bytes(data)
   need(exact(warm.build(True,root=root),packet),'Warm restored canonical mismatch')
 return {'status':'PASS','source_sha256':PIN,'dependency_pins':PINS,'parent_receipt_pins':RECEIPT_PINS,'counts':dict(counts),'forms':records,'scope':'Independent complete source/cut/finalizer/count/domain audit of eight actual complete forms; exact degree transfers by full polynomial identity and is independently attained by literal modular specialization. No full universal Pell witness materialized.'}
if __name__=='__main__':
 p=argparse.ArgumentParser()
 for n in ('source','root','output'):p.add_argument('--'+n,type=Path,required=True)
 p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.source.resolve(),a.root.resolve())
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Receipt mismatch')
 a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
