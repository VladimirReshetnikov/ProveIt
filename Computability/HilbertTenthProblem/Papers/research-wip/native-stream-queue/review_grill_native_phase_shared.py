#!/usr/bin/env python3
"""Independent all-coordinate proof and API audit of native Grill phase sharing."""
import argparse,copy,hashlib,json,random,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
import sympy as sp
SOURCE_SHA256='760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069'
PARENT_SHA256='80abbb7a293ba1051fc1d2559c7f8aac5a2f28947535573be49c8c49f5f3e7b7'

def need(x,msg):
 if not x:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def load(path,digest,name):
 data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==digest,'Source pin '+name)
 m=types.ModuleType(name);m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m

def evalrows(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  need(n not in e and op in ('+','-','*'),'Source SSA')
  aa=e[a] if type(a)is str else a;bb=e[b] if type(b)is str else b
  e[n]=aa+bb if op=='+' else aa-bb if op=='-' else aa*bb
 return e
def at(e,x):return e[x] if type(x)is str else x

def affine_certificate(p):
 m=p['phase_count'];hats=[f'Shat{i}' for i in range(2*m)];symbols={x:sp.Symbol(x) for x in hats};defs={n:(o,a,b) for n,o,a,b in p['source']};e=dict(symbols)
 def ev(x):
  if type(x)is int:return sp.Integer(x)
  if x not in e:
   need(x in defs,'Unexpected independent phase atom '+x);o,a,b=defs[x];aa=ev(a);bb=ev(b);e[x]=aa+bb if o=='+' else aa-bb if o=='-' else aa*bb
  return e[x]
 sel=[symbols[x]-1 for x in hats]
 wanted=[sum(sel),sum((i//2+1)*a for i,a in enumerate(sel)),sum(((i//2-1)%m+1)*a for i,a in enumerate(sel))]
 result={}
 for key,w in zip(('J','Q','Next'),wanted):
  expr=sp.expand(ev(p['interfaces'][key]));need(sp.expand(expr-w)==0,'Phase identity in all supplied hats '+key)
  poly=sp.Poly(expr,*symbols.values());need(poly.total_degree()==1,'Exact affine degree');result[key]=str(expr)
 return result

def graph_certificate(old,new):
 names=old['parameters']+old['auxiliaries'];intern={}
 def node(key):
  if key not in intern:intern[key]=len(intern)
  return intern[key]
 def graph(p):
  m=p['phase_count'];forms={
   'J':tuple([1]*(2*m)+[-2*m]),
   'Q':tuple([i//2+1 for i in range(2*m)]+[-m*(m+1)]),
   'Next':tuple([(i//2-1)%m+1 for i in range(2*m)]+[-m*(m+1)])}
  cuts={p['interfaces'][k]:v for k,v in forms.items()};e={n:node(('supplied',n)) for n in names}
  def value(x):return e[x] if type(x)is str else node(('integer',x))
  for n,op,a,b in p['polynomial_source']:
   need(n not in e and (type(a)is int or a in e) and (type(b)is int or b in e),'Closed whole DAG')
   e[n]=node(('proven all-hat affine',cuts[n])) if n in cuts else node((op,value(a),value(b)))
  return e,value
 aa,av=graph(old);bb,bv=graph(new)
 need(exact(old['comparisons'],new['comparisons']),'Literal comparison list')
 for a,b in old['comparisons']:need(av(a)==bv(a) and av(b)==bv(b),'Whole comparison operand')
 need(aa[old['output']]==bb[new['output']],'Complete polynomial identity')
 for name in old.get('unit_factors',[]):need(aa[name]==bb[name],'Exact native factor')
 for key,x in old['interfaces'].items():need(av(x)==bv(new['interfaces'][key]),'Active semantic interface '+key)
 need(exact(old['polynomial_source'][len(old['source']):],new['polynomial_source'][len(new['source']):]),'Literal finalizer retained')
 return len(old['comparisons'])

def ledger(p):
 names=p['parameters']+p['auxiliaries'];seen=set(names);degree={n:1 for n in names};live={p['output']};c=Counter()
 for n,op,a,b in p['polynomial_source']:
  need(type(n)is str and n not in seen and op in ('+','-','*'),'SSA gate')
  need(all(type(x)is int or type(x)is str and x in seen for x in (a,b)),'Typed operands')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0;degree[n]=da+db if op=='*' else max(da,db);seen.add(n);c['M' if op=='*' else 'A']+=1
 for n,op,a,b in reversed(p['polynomial_source']):need(n in live,'Dead paid gate');live.update(x for x in (a,b) if type(x)is str)
 need(set(names)<=live,'Unused coordinate')
 need(len(p['polynomial_source'])==sum(c.values())==p['polynomial_ledger']['operations'],'Paid full gate total')
 need(all(c[k]==p['polynomial_ledger'][k] for k in ('M','A')),'Paid gate types')
 need(p['polynomial_ledger']['degree_upper']==degree[p['output']] and p['exact_degree'] is None,'Formal upper bound only')
 need(p['operations']==len(p['source']) and p['wrapper_operations']==sum(not n.startswith(p['native_prefix']) for n,op,a,b in p['source']),'Active source counts')
 return dict(c)

def verify(source,root):
 s=load(source,SOURCE_SHA256,'_review_phase_child');parentpath=source.with_name('grill_tag_native_word_closure.py')
 if not parentpath.exists():parentpath=root/'grill_tag_native_word_closure.py'
 parent=load(parentpath,PARENT_SHA256,'_review_phase_parent');c=Counter();rng=random.Random(209);forms=[]
 programs=((0,),(1,),(0,1,1),(2,0,1),(0,0),(0,2),(0,0,0),(0,1,2,0),(2,0,1,0,2))
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):c['malformed_rejections']+=1;return
  raise ValueError('Malformed input accepted')
 for program in programs:
  for unit in (False,True):
   p=s.build(program,unit_product=unit,root=root);old=s.canonical_parent(p,root=root)
   need(exact(old,parent.build(program,unit_product=unit,root=root)),'Independently loaded canonical parent')
   for field in ('parameters','auxiliaries','maps','groups_U','groups_V','K','scope','scale_exponent','region_exponents','projection_aliases','root_coordinate','unit_factors'):
    need(exact(p.get(field),old.get(field)),'Unchanged native/domain metadata '+field)
   affine_certificate(old);affine_certificate(p);c['expanded_affine_identities']+=6
   c['formal_residual_identities']+=graph_certificate(old,p);c['complete_formal_polynomial_identities']+=1
   ledger(p);c['complete_ledger_liveness_degree_checks']+=1
   need(p['polynomial_ledger']['operations']<=old['polynomial_ledger']['operations'],'No worse whole-source schedule')
   if len(program)==1:
    need(exact(p['source'],old['source']) and exact(p['polynomial_source'],old['polynomial_source']) and exact(p['interfaces'],old['interfaces']),'Exact one-phase no-op');c['one_phase_noop_forms']+=1
   if program==(0,1,1):need(p['polynomial_ledger']['operations']==(209 if unit else 233),'Default whole-source count')
   removed=set(p['phase_sharing']['removed_source_registers'])
   def scan(v):
    if type(v)is dict:
     for value in v.values():scan(value)
    elif type(v)in(tuple,list):
     for value in v:scan(value)
    elif type(v)is str:need(v not in removed,'Stale active metadata register '+v)
   scan({k:v for k,v in p.items() if k!='phase_sharing'});c['active_metadata_scans']+=1
   for j in range(10):
    values={n:rng.randrange(-3,4) if j>=5 else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
    a=evalrows(old['polynomial_source'],values);b=evalrows(p['polynomial_source'],values)
    need(a[old['output']]==b[p['output']],'Numeric complete output')
    need([at(a,x)-at(a,y) for x,y in old['comparisons']]==[at(b,x)-at(b,y) for x,y in p['comparisons']],'Numeric all residuals');c['complete_numeric_identities']+=1;c['signed_cases']+=j>=5
   values={n:Fraction(rng.randrange(-2,3),rng.randrange(1,4)) for n in p['parameters']+p['auxiliaries']};a=evalrows(old['polynomial_source'],values);b=evalrows(p['polynomial_source'],values);need(a[old['output']]==b[p['output']],'Rational full identity');c['rational_cases']+=1
   for field in ('source','polynomial_source','interfaces','comparisons','phase_sharing','polynomial_ledger'):
    bad=copy.deepcopy(p);bad[field]=None;reject(lambda bad=bad:s.checked(bad,root=root))
   # Equal-value float/Boolean constants cannot pass canonical source checking.
   for typ in (float,bool):
    bad=copy.deepcopy(p);i,j=next((i,j) for i,row in enumerate(bad['polynomial_source']) for j in (2,3) if type(row[j])is int and (typ is float or row[j]in(0,1)))
    row=list(bad['polynomial_source'][i]);row[j]=typ(row[j]);bad['polynomial_source'][i]=tuple(row);reject(lambda bad=bad:s.checked(bad,root=root))
   for getter in (lambda:s.build(program,unit_product=unit,root=root),lambda:s.canonical_parent(p,root=root),lambda:s.polynomial_source(p,root=root)):
    obj=getter();saved=copy.deepcopy(obj);obj.clear();need(exact(getter(),saved),'Public mutable cache');c['defensive_copies']+=1
   forms.append(dict(program=list(program),unit_product=unit,ledger=p['polynomial_ledger'],saved=p['phase_sharing']['saved']))
 for bad in (None,(),[0],(True,),(1.0,),(-1,)):
  reject(lambda bad=bad:s.build(bad,root=root))
 p=s.build(root=root);values={n:1 for n in p['parameters']+p['auxiliaries']}
 for bad in (True,1.0,0,-1,Fraction(1,2),None):reject(lambda bad=bad:s.evaluate(p,dict(values,x=bad),root=root))
 for bad in (0,1,None):reject(lambda bad=bad:s.evaluate(p,values,signed=bad,root=root))
 bad=copy.deepcopy(s.canonical_parent(p,root=root));bad['scope']='altered';reject(lambda:s.rewrite(bad,root=root))
 return dict(status='PASS_INDEPENDENT_NATIVE_GRILL_PHASE_SHARING',helper_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_sha256=SOURCE_SHA256,parent_sha256=PARENT_SHA256,checks=dict(c),forms=forms,scope='Exact whole-polynomial equivalence on same coordinates, including all native factors and paid finalizers; no new native theorem, duration bound or universality claim.')

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=Path(__file__).with_name('grill_tag_native_phase_sharing.py'));ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=json.loads(json.dumps(verify(a.source,a.root),sort_keys=True))
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Saved independent receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:r[k] for k in ('status','checks')},sort_keys=True))
