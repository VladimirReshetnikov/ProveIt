"""Independent exact polynomial audit of the frozen sparse wire projection."""
import argparse,hashlib,importlib.util,itertools,json,sys
from pathlib import Path
SOURCE_SHA='bfa23f92958b6beb1a8a782ea2d478257d4d11b52f4d5559509913d21082e950'
PRODUCER_SHA='1c35e0104730dfe99c9be4c350b49d66646d8e0dd7c7580b262367f1070d02c8'
def load(p,name,pin):
 if hashlib.sha256(p.read_bytes()).hexdigest()!=pin:raise ValueError('source pin mismatch')
 spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
def add(*ps):
 out={}
 for p in ps:
  for mon,c in p.items():out[mon]=out.get(mon,0)+c
 return {m:c for m,c in out.items() if c}
def mul(p,q):
 out={}
 for a,c in p.items():
  for b,d in q.items():k=tuple(sorted(a+b));out[k]=out.get(k,0)+c*d
 return {m:c for m,c in out.items() if c}
def sub(p,expr):
 out={}
 for mon,c in p.items():
  term={():c}
  for i in mon:term=mul(term,expr[i])
  out=add(out,term)
 return out
def same(a,b):
 return type(a) is type(b) and (a.keys()==b.keys() and all(same(a[k],b[k]) for k in a) if isinstance(a,dict) else len(a)==len(b) and all(same(x,y) for x,y in zip(a,b)) if isinstance(a,list) else a==b)
def run(source,producer):
 if not __debug__:raise RuntimeError('review requires assertions enabled')
 mod=load(Path(source),'independent_sparse_projection',SOURCE_SHA);m=load(Path(producer),'independent_sparse_producer',PRODUCER_SHA);counts={};cases=[]
 def check(k,v):assert v,k;counts[k]=counts.get(k,0)+1
 for K,M,T,orthant,partial,endpoint in [(1,1,0,False,False,False),(1,1,1,False,False,False),(1,2,2,False,False,False),(1,3,2,True,False,False),(2,2,1,True,False,True),(2,1,3,False,True,False),(2,1,2,True,True,True)]:
  table=m.LocalTable.from_mapping(K,{p:p for p in itertools.product(range(K+1),repeat=3)})
  conf={-10**40:(0,0,1)} if M==1 else {0:(0,0,1),2:(1,0,0)} if M==2 else {0:(1,1,1)}
  allowed=[(0,0,0),(1,0,0),(0,0,1)] if partial else None
  kwargs={'orthant_exact':orthant,'allowed_inputs':allowed}
  if endpoint:kwargs['endpoint']={999:(M if M<=K else 1,0,0)}
  old,meta=m.compile_history(table,conf,T,**kwargs);actual=mod.project(m,old);definitions=dict(zip(old.residual_names,old.residuals));expr=[];names=[];removed=[]
  for i,name in enumerate(old.names):
   eliminate=('.stream.' in name or '.mass.' in name or ('.g.' in name and '.out.' in name) or ('.sort.' in name and name.endswith(('.xmax','.zmax'))))
   if eliminate:
    row=dict(definitions[name].terms);check('monic_definition',row.pop((i,),None)==1)
    check('topological_definition',all(j<i for mon in row for j in mon))
    expression=sub({mon:-c for mon,c in row.items()},expr);expr.append(expression);removed.append(name)
    maximum=2 if '.mass.' in name else 1
    check('restoration_degree',max(map(len,expression),default=0)<=maximum)
    if '.mass.' in name:
     stem,tail=name.split('.mass.');particle=tail.split('.')[0]
     consumers=[label for label,p in zip(old.residual_names,old.residuals) if any(i in mon for mon,c in p.terms) and label!=name]
     check('incoming_only_table_moment_consumers',all(label.startswith(stem+'.g.'+particle+'.input.') for label in consumers) and len(consumers)==1)
   else:expr.append({(len(names),):1});names.append(name)
  mapped=[sub(dict(p.terms),expr) for p in old.residuals]
  kept=[p for label,p in zip(old.residual_names,mapped) if label not in set(removed)]
  check('independent_all_restoration_polynomials',[dict(p.terms) for p in actual['restore']]==expr)
  check('independent_all_residual_polynomials',[dict(p.terms) for p in actual['residuals']]==kept)
  check('omitted_rows_symbolic_zero',all(not p for label,p in zip(old.residual_names,mapped) if label in set(removed)))
  check('complete_expanded_SOS_identity',add(*(mul(p,p) for p in mapped))==add(*(mul(p,p) for p in kept)))
  S=3 if partial else (K+1)**3
  extra=0 if not endpoint else 2*M if sum(sum(x) for x in kwargs['endpoint'].values())==M else 1
  check('counts_with_endpoint_and_orthant',len(names)==T*(M*(S+7)+4*M*(M-1)) and len(kept)==T*(10*M+4*M*(M-1)+2*M*orthant)+extra)
  check('savings_formula',len(removed)==T*(7*M+M*(M-1)))
  check('all_retained_degrees',all(max(map(len,p),default=0)<=2 for p in kept))
  check('canonical_natural_graph',[p.evaluate(actual['values']) for p in actual['restore']]==old.values)
  cases.append({'K':K,'M':M,'T':T,'orthant':orthant,'partial':partial,'endpoint':endpoint,'variables':len(names),'residuals':len(kept),'removed':len(removed)})
 return {'status':'PASS','source_sha256':SOURCE_SHA,'producer_sha256':PRODUCER_SHA,'checks':counts,'cases':cases,'scope':'Exact independent sparse polynomial substitution and complete SOS identity on these emitted instances; natural-zero theorem justified separately by the general layer induction.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source',required=True,type=Path);p.add_argument('--producer',required=True,type=Path);p.add_argument('--output',required=True,type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.source,a.producer)
 if a.expect and not same(r,json.loads(a.expect.read_text())):raise AssertionError('receipt differs')
 a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps(r['checks'],sort_keys=True))
