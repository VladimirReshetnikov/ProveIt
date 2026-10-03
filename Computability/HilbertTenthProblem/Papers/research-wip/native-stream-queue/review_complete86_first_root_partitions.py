#!/usr/bin/env python3
"""Independent finite-family/source review, not a search over general circuits."""
import argparse,copy,hashlib,json,random,tempfile,subprocess,sys
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from math import prod,isqrt
from pathlib import Path
PINS={'complete86_first_root_partitions.py':'b139097ed009580cfe8fc7707e373ec9ecafdecb886bd2cf037d615a06d35988',
'complete86_first_root_partitions.json':'7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5',
'complete86_first_root_partitions.md':'7325cf4fcf88bd5c20bd3d556eef7c8a313f3aee914e637483dc065d2417c2e0'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
CONST=['Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF']
def need(v,s):
 if not v:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def encoded(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def scalar(rows,vals):
 e=dict(vals)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b]
  e[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return e
def prune(rows,outputs):
 wanted=set(outputs);keep=[]
 for row in reversed(rows):
  if row[0] in wanted:
   keep.append(row);wanted.update(x for x in row[2:] if type(x)is str)
 return list(reversed(keep))
def count(rows,outputs,free):
 ready=set(free);names=set();c=Counter()
 for n,op,a,b in rows:
  need(n not in ready and op in ('+','-','*'),'closed unique gate')
  need(all(type(v)is int or type(v)is str and v in ready for v in (a,b)),'exact operand')
  c['M' if op=='*' else 'A']+=1;ready.add(n);names.add(n)
 need(prune(rows,outputs)==rows,'all gates live')
 leaves={x for row in rows for x in row[2:] if type(x)is str and x not in names}
 need(leaves==set(free),'same complete free coordinates')
 return {'operations':len(rows),'M':c['M'],'A':c['A'],'positive_witnesses':len(free)-7,'all_gates_live':True}
@lru_cache(None)
def partitions(mask):
 if not mask:return ((),)
 first=mask&-mask;rest=mask^first;result=[];sub=rest
 while True:
  group=first|sub
  for tail in partitions(rest^sub):result.append((group,)+tail)
  if sub==0:break
  sub=(sub-1)&rest
 return tuple(result)
def objective(core,weights,residuals,partition,anchor):
 sums=[sum(w for i,w in enumerate(weights) if mask>>i&1) for mask in partition]
 g=len(sums);n=len(weights);m=len(residuals)
 cost=core+n-g
 if anchor is None:cost+=3*(m+g)-1;degree=2*max(residuals+sums)
 else:
  others=residuals+[w for i,w in enumerate(sums) if i!=anchor]
  cost+=1 if not others else 3*len(others)+2
  degree=sums[anchor]+(2*max(others) if others else 0)
 return cost,degree

def dense(rows,values,prime):
 def trim(v):
  while len(v)>1 and not v[-1]:v.pop()
  return v
 env=copy.deepcopy(values)
 for n,op,a,b in rows:
  a=[a%prime] if type(a)is int else env[a];b=[b%prime] if type(b)is int else env[b]
  if op=='*':
   c=[0]*(len(a)+len(b)-1)
   for i,x in enumerate(a):
    if x:
     for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%prime
  else:c=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))]
  env[n]=trim(c)
 return env
def verify(root,subject_root):
 root=Path(root);subject_root=Path(subject_root)
 for n,h in PINS.items():need(sha((subject_root/n).read_bytes())==h,'subject pin '+n)
 saved=json.loads((subject_root/'complete86_first_root_partitions.json').read_text())
 for n,h in saved['parent_pins'].items():need(sha((root/n).read_bytes())==h,'actual asymmetric dependency '+n)
 path=subject_root/'complete86_first_root_partitions.py';api={'__name__':'_independent_root_partitions','__file__':str(path)};exec(compile(path.read_bytes(),str(path),'exec'),api)
 need(exact(api['PINS'],saved['parent_pins']),'dependency inventory')
 load=lambda stem:json.loads((root/(stem+'.json')).read_text())
 asym=load('complete75_asymmetric_scale_tradeoffs')['source'];direct={x['name']:x for x in load('complete75_asymmetric_linear_gap_tradeoffs')['direct_transfers']}
 specs=[]
 for name,normalized,comparison in [('asymmetric_normalized',True,False),('asymmetric_ordinary',False,False),('asymmetric_comparison',False,True)]:
  specs.append((name,asym[0 if normalized else 1]['source'],[22,18,32,56 if normalized else 24,7,3,34 if normalized else 22,7],int(comparison)))
 for prefix in ['linear','auxgap']:
  for family in ['coupled_units','uncoupled_units','coupled_comparison','uncoupled_comparison','six_comparisons']:
   uncoupled=family.startswith('uncoupled') or family=='six_comparisons'
   key=('linear_90_degree132' if uncoupled else 'linear89') if prefix=='linear' else ('gap_91_degree128' if uncoupled else 'gap_90_degree131')
   specs.append((prefix+'_'+family,direct[key]['source'],[22,18,20,20 if prefix=='auxgap' else 24,7,3,22,6 if uncoupled else 7],2 if family=='six_comparisons' else int(family.endswith('comparison'))))
 need([x[0] for x in specs]==api['KINDS'],'exact thirteen actual asymmetric bases')
 counts=Counter();families=[];new_bases={};old_bases={};rng=random.Random(8617987)
 # Full symbolic first-factor graph identity in independent T,L,k.
 def add(a,b,sgn=1):
  d=a.copy()
  for m,v in b.items():d[m]=d.get(m,0)+sgn*v
  return {m:v for m,v in d.items() if v}
 def mul(a,b):
  d={}
  for m,v in a.items():
   for n,w in b.items():
    q=tuple(x+y for x,y in zip(m,n));d[q]=d.get(q,0)+v*w
  return {m:v for m,v in d.items() if v}
 T={(1,0,0):1};L={(0,1,0):1};k={(0,0,1):1};gap=add(T,L,-1)
 need(add(mul(gap,gap),mul(L,add(add(gap,gap),k,-1)))==add(mul(T,T),mul(L,add(L,k)),-1),'all-value graph identity')
 for kind,origin,weights,m in specs:
  factors=FACTORS[:];pairs=[];res=[]
  if m:del factors[6];del weights[6];pairs.append(['ic22','R16']);res.append(22)
  if m==2:factors.pop();weights.pop();pairs.append(['H17','aux_u_rhs']);res.append(6)
  parent=api['canonical_parent'](root,kind);b=api['base'](root,kind);old_bases[kind]=parent;new_bases[kind]=b
  targets=factors+[v for pair in pairs for v in pair];old=prune(origin,targets)
  need(exact(old,parent['source']) and exact(pairs,b['ordinary_comparisons']) and factors==b['factors'] and weights==b['weights'],'literal independently selected parent/core/weights')
  d={n:[op,a,bb] for n,op,a,bb in old}
  need(d['wn2']==['*','w','q'] and d['sn2']==['*','s','n2'] and d['n2']==['*','Lbig','q'],'actual asymmetric scale, not symmetric preliminary family')
  need(d['ksn2']==['*','R10b','sn2'] and d['R10b']==['+','eta','zeta'],'actual k is computed eta+zeta')
  need([n for n,op,a,bb in old if 'tau_gap' in (a,bb)]==['tau_square','twice_tau_gap'],'only private gap users')
  expected=[]
  for n,op,a,bb in old:
   if n=='tau_square':expected.append([n,'*','tau_root','tau_root'])
   elif n=='norm_first':expected += [['first_next','+','first_root_base','R10b'],['first_product','*','first_root_base','first_next'],['norm_first','-','tau_square','first_product']]
   elif n not in ['twice_tau_gap','first_signed_gap','first_cross']:expected.append([n,op,a,bb])
  need(exact(expected,b['source']),'complete five-gate transformation')
  newcount=count(b['source'],targets,b['witnesses']+CONST+['x']);oldcount=count(old,targets,parent['witnesses']+CONST+['x'])
  need(exact(newcount,b['core_ledger']) and oldcount['M']==newcount['M'] and oldcount['A']==newcount['A']+1,'complete paid core one-addition saving');counts['actual_core_ledgers']+=2
  n=len(factors);allp=partitions((1<<n)-1);need(len(set(allp))==len(allp)=={6:203,7:877,8:4140}[n],'unique complete subset-recursive partitions')
  best={};choices=0
  for partition in allp:
   for anchor in [None]+list(range(len(partition))):
    cost,deg=objective(newcount['operations'],weights,res,partition,anchor);best[cost]=min(best.get(cost,10**9),deg);choices+=1
  auth=next(f for f in saved['census']['families'] if f['kind']==kind)
  need(len(allp)==auth['partitions'] and choices==auth['finalizer_choices'],'independent complete combinatorial counts')
  need(best=={r['operations']:r['exact_degree'] for r in auth['best_by_cost']},'every finite minimum by operation count')
  families.append({'kind':kind,'core':newcount,'weights':weights,'retained_residual_degrees':res,'partitions':len(allp),'choices':choices,'best_by_cost':[[c,best[c]] for c in sorted(best)]})
  counts['partitions']+=len(allp);counts['finalizer_choices']+=choices
 def front(points):
  out=[];bound=10**9
  for cost,degree in sorted(set(points)):
   if degree<bound:out.append([cost,degree]);bound=degree
  return out
 frontier=front([tuple(r) for f in families for r in f['best_by_cost']]);oldfront=load('complete75_asymmetric_linear_gap_tradeoffs')['combined_frontier']
 combined=front([tuple(r) for r in frontier]+[(r['operations'],r['exact_degree']) for r in oldfront])
 need(frontier==[[r['operations'],r['exact_degree']] for r in saved['census']['frontier']],'new thirteen-base frontier')
 need(combined==[[r['operations'],r['exact_degree']] for r in saved['census']['combined_frontier']],'union with complete prior asymmetric frontier')
 plans=[];degree_cases=[]
 for rec in saved['winner_ledgers']:
  kind=rec['kind'];b=new_bases[kind];parent=old_bases[kind];p=api['build'](root,kind,rec['partition'],rec['anchor']);rows=p['polynomial_source'];g=rec['partition'];anchor=rec['anchor']
  need(rows[:len(b['source'])]==b['source'],'literal complete base prefix')
  ledger=count(rows,[p['output']],b['witnesses']+CONST+['x']);need(exact(ledger,p['ledger']) and exact(ledger,rec['ledger']),'full winner source ledger')
  need(sha(encoded(rows))==rec['complete_source_sha256'],'saved complete source hash')
  cert=count(p['certificate_source'],p['group_products']+[v for pair in b['ordinary_comparisons'] for v in pair],b['witnesses']+CONST+['x'])
  need(exact(cert,p['certificate_ledger']) and cert['operations']==rec['certificate_operations'] and p['equations']==rec['equations']==len(g)+len(b['ordinary_comparisons']),'independent complete certificate ledger/equations');counts['emitted_certificate_ledgers']+=1
  masks=tuple(sum(1<<i for i in q) for q in g);cost,deg=objective(b['core_ledger']['operations'],b['weights'],b['residual_degrees'],masks,anchor)
  need(cost==len(rows) and deg==p['degree_certificate']['exact_degree'],'independent complete finalizer objective')
  for case in range(4):
   vals={n:rng.randrange(-3,5) for n in b['witnesses']+CONST+['x']}
   if case==0:vals={n:abs(v)+1 for n,v in vals.items()}
   if case==3:vals={n:Fraction(v,3) for n,v in vals.items()}
   e=scalar(rows,vals);oldvals=dict(vals);oldvals['tau_gap']=oldvals.pop('tau_root')-e['first_root_base'];oe=scalar(parent['source'],oldvals)
   need(all(e[f]==oe[f] for f in b['factors']),'all actual factor graph identities')
   products=[prod(e[b['factors'][i]] for i in q) for q in g]
   at=lambda v:e[v] if type(v)is str else v
   S=sum((at(a)-at(bb))**2 for a,bb in b['ordinary_comparisons'])+sum((v-1)**2 for i,v in enumerate(products) if i!=anchor)
   need(e[p['output']]==(S if anchor is None else products[anchor]*(1+S)-1),'whole emitted source versus independent finalizer')
   # The restored old source has unchanged ordinary ports too; manual old output equals the child.
   need(all(e[v]==oe[v] for pair in b['ordinary_comparisons'] for v in pair),'retained ordinary rows')
   counts['complete_signed_rational_graph_cases']+=1
  plans.append((rec,p));counts['emitted_winner_ledgers']+=1
 # Two independent modular lines per base; evaluate every complete winner without leading substitutions.
 for kind,b in new_bases.items():
  selected=[(rec,p) for rec,p in plans if rec['kind']==kind]
  for line,(B,prime) in enumerate([(64,1031),(128,1061)]):
   # A deterministic retry only avoids accidental specialization cancellation; all whole coefficients are still evaluated.
   for trial in range(32):
    vals={n:[i+2,(i+trial)%5+1] for i,n in enumerate(b['witnesses']+['x'])}
    vals.update({n:[v] for n,v in dict(Bm1=B-1,Kconstant=7*B+5,twice_cell_bits=2*(B.bit_length()-1),inner_bits=5,MC=B-6,MF=B+9).items()})
    env=dense(b['source'],vals,prime)
    if all(len(env[f])-1==d for f,d in zip(b['factors'],b['weights'])):break
   else:raise ValueError('no factor degree witness')
   counts['full_factor_coefficient_expansions']+=len(b['factors'])
   for a,bb in b['ordinary_comparisons']:
    aa=env[a];bs=env[bb];r=[((aa[i] if i<len(aa) else 0)-(bs[i] if i<len(bs) else 0))%prime for i in range(max(len(aa),len(bs)))];
    while len(r)>1 and r[-1]==0:r.pop()
    need(len(r)-1==b['residual_degrees'][b['ordinary_comparisons'].index([a,bb])],'actual retained residual degree');counts['residual_coefficient_expansions']+=1
   for rec,p in selected:
    e=dense(p['polynomial_source'][len(b['source']):],env,prime);out=e[p['output']]
    # Rare SOS leading coefficient cancellation modulo p can occur; a rational theorem is unaffected, but this chosen certificate must attain its degree.
    need(len(out)-1==rec['exact_degree'] and out[-1]!=0,'actual full winner degree and nonzero modular coefficient')
    degree_cases.append({'kind':kind,'operations':rec['operations'],'degree':len(out)-1,'prime':prime,'trial':trial,'coefficient':out[-1],'all_coefficients_sha256':sha(encoded(out))});counts['full_winner_degree_expansions']+=1
 # Direct zero-lift boundary: both N0 signs imply a positive restored gap.
 signs=set()
 for Lval in range(1,81):
  for kval in range(2,41):
   for eps in (-1,1):
    Tval=isqrt(Lval*Lval+Lval*kval+eps)
    if Tval*Tval==Lval*Lval+Lval*kval+eps:
     need(Tval>Lval and (Tval-Lval)**2+Lval*(2*(Tval-Lval)-kval)==eps,'positive inverse before old theorem');signs.add(eps);counts['both_sign_restoration_cases']+=1
 need(signs=={-1,1},'both unit signs')
 # k>=2 is essential to this short isolated argument: k=1,L=T=1,N0=-1 has zero gap.
 need(1**2-1*(1+1)==-1,'excluded isolated k1 boundary')
 for rec in saved['census']['frontier']:
  p=api['build'](root,rec['kind'],rec['partition'],rec['anchor']);b=p['base']
  def reject(fn):
   try:fn()
   except (ValueError,TypeError,KeyError):counts['malformed_rejections']+=1
   else:raise ValueError('bad caller accepted')
  for key in p:
   bad=copy.deepcopy(p);del bad[key];reject(lambda bad=bad:api['checked'](root,bad))
  for i in [0,len(p['polynomial_source'])//2,len(p['polynomial_source'])-1]:
   bad=copy.deepcopy(p);bad['polynomial_source'][i][1]='*' if bad['polynomial_source'][i][1]!='*' else '+';reject(lambda bad=bad:api['checked'](root,bad))
  for value in [22.0,True,23]:
   bad=copy.deepcopy(p);bad['base']['weights'][0]=value;reject(lambda bad=bad:api['checked'](root,bad))
  vals={n:1 for n in b['witnesses']+CONST+['x']}
  reject(lambda:api['coordinate'](root,p,vals,to_parent=True,positive=True))
  oldvals={n:1 for n in old_bases[rec['kind']]['witnesses']+CONST+['x']};forward=api['coordinate'](root,p,oldvals,positive=True)
  need(api['coordinate'](root,p,forward,to_parent=True,positive=True)==oldvals,'positive forward roundtrip')
  obj=api['canonical_parent'](root,rec['kind']);obj['weights'][0]=True;need(api['canonical_parent'](root,rec['kind'])['weights'][0]==12,'private cache copy');counts['cache_copy_checks']+=1
 with tempfile.TemporaryDirectory(prefix='independent-root-partitions-') as temp:
  path2=Path(temp)
  for n in saved['parent_pins']:(path2/n).write_bytes((root/n).read_bytes())
  api['canonical_parent'](path2)
  for n in ['complete75_asymmetric_linear_gap_tradeoffs.json','complete75_asymmetric_scale_tradeoffs.md']:
   raw=(path2/n).read_bytes();(path2/n).write_bytes(raw+b'\n')
   try:api['canonical_parent'](path2)
   except ValueError:counts['warm_pin_rejections']+=1
   else:raise ValueError('warm source pin bypass')
   (path2/n).write_bytes(raw)
 proc=subprocess.run([sys.executable,'-O',str(path),'--root',str(root)],capture_output=True,text=True,timeout=30)
 need(proc.returncode!=0 and 'without -O' in proc.stderr,'optimized mode rejected');counts['optimized_rejections']+=1
 return {'status':'PASS_INDEPENDENT_ACTUAL_ASYMMETRIC_ROOT_PARTITIONS','review_source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'parent_pins':saved['parent_pins'],'counts':dict(counts),'families':families,'new_frontier':frontier,'combined_frontier':combined,'complete_degree_witnesses':degree_cases,
 'scope':'Thirteen actual asymmetric bases only. Independent subset partition census, complete101 winner ledgers, exact graph proof and modular full source coefficients. Inherits uniform parent factor leaders, no full universal zero materialized, no general circuit optimum.'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--subject-root',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root,v.subject_root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'combined_frontier':r['combined_frontier']},sort_keys=True))
if __name__=='__main__':main()
