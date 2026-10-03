#!/usr/bin/env python3
"""Independent complete four-form asymmetric scale/circuit audit."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
SUBJECT_PINS={'complete113_asymmetric_retained109.py': '5017530a67107651cbde1cbfd81e4a2cf0aad294bb81997789e8e749a1ea2368', 'complete113_asymmetric_retained109.json': '8a037d2830ef3cbbfe7f0b02b71b5337ffac8a3e34cf8391c09257d0babb9f24', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0'}
PARENT_PINS={'complete74_gap_selective_projection113.py': '573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4', 'complete74_gap_selective_projection113.json': '2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3', 'complete74_gap_selective_projection113.md': '3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa', 'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_positive_elimination.json': '03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703', 'complete75_positive_elimination.md': '59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b', 'complete75_positive_root89.py': 'f850ee8cd5e00b9235a8f192d2f95f6b27cf72a40c3f6b6e3fa054700d793c72', 'complete75_positive_root89.md': '7b85195a800b909e3bf6e55fa85decfaa08299cf1e100efa866659571d192085', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete113_main_input_units111.py': '152905dd07e507289fe9f321982f5e680ec34b6a3ef23f7205bd370ad6623d16', 'complete113_main_input_units111.json': 'b9702ea066114aec3aef374a480fb2049f47a47d1daf580ea42e595107ebee87', 'complete113_main_input_units111.md': '9f73c0d51f5e1fe9237b0ffc3cbbba49f93b08a0b6242693425f0e086897905f', '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992'}
MODES=('sos','pair','triple','two_pairs')
GROUPS={'sos':(), 'pair':(('main','input'),), 'triple':(('main','input','aux'),), 'two_pairs':(('first','main'),('input','aux'))}
CONST=('Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF')
def need(v,msg):
 if not v:raise AssertionError(msg)
def sha(v):return hashlib.sha256(v).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(tuple,list):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def add(a,b,sign=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items()if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():k=tuple(sorted(m+n));c[k]=c.get(k,0)+v*w
 return {m:v for m,v in c.items()if v}
def atom(v):return {():v}if type(v)is int else{(v,):1}
def power(v,n):
 out=atom(1)
 for _ in range(n):out=mul(out,v)
 return out
def prod(values,one=1):
 for v in values:one*=v
 return one
def run(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b];e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def ledger(rows,free,ports):
 seen=set(free);deps={};m=0;degree={v:0 if v in CONST else 1 for v in free}
 for n,o,a,b in rows:
  need(type(n)is str and n not in seen and o in('+','-','*'),'exact fresh row')
  need(all(type(v)is int or type(v)is str and v in seen for v in(a,b)),'exact closed operands')
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b];degree[n]=da+db if o=='*'else max(da,db)
  deps[n]=(a,b);seen.add(n);m+=o=='*'
 live=set();todo=list(ports)
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 need(set(deps)<=live and set(free)<=live,'all supplied ports and gates live')
 return {'operations':len(rows),'M':m,'A':len(rows)-m,'all_gates_live':True,'free':sorted(free),'literal_degree_upper_bound':max(0 if type(v)is int else degree[v]for v in ports)}
def finalizer(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 name='square_0'
 for i in range(1,len(pairs)):
  new=f'sum_{i}';out.append([new,'+',name,f'square_{i}']);name=new
 return out,name

class DAG:
 def __init__(self):self.nodes={}
 def intern(self,x):
  if x not in self.nodes:self.nodes[x]=len(self.nodes)
  return self.nodes[x]
 def a(self,x):return self.intern(('atom',type(x).__name__,x))
 def op(self,o,a,b):return self.intern((o,a,b))
 def run(self,rows,free):
  e={v:self.a(v)for v in free}
  for n,o,a,b in rows:e[n]=self.op(o,self.a(a)if type(a)is int else e[a],self.a(b)if type(b)is int else e[b])
  return e

def structural(parent,p,mode,asymmetric):
 rows=copy.deepcopy(parent['source']);index=next(i for i,r in enumerate(rows)if r[0]=='wn2');need(rows[index]==['wn2','*','w','n2'],'actual original X scale')
 if asymmetric:rows[index][-1]='q'
 free=parent['polynomial_ledger']['free'];d=DAG();old=d.run(rows,free);new=d.run(p['source'],free)
 get=lambda env,v:d.a(v)if type(v)is int else env[v]
 units={'first':d.op('+',old['tau_square'],old['L9']), 'main':d.op('-',old['L15'],old['Ac2']), 'input':d.op('-',old['mu2'],old['scaled_kappa2']), 'aux':d.op('+',old['L17'],old['aux_y2'])}
 combined=[]
 for group in GROUPS[mode]:
  v=units[group[0]]
  for name in group[1:]:v=d.op('*',v,units[name])
  combined.append((v,d.a(1)))
 norm_positions={'first':3,'main':7,'input':12,'aux':9};removed={norm_positions[name]for group in GROUPS[mode]for name in group}
 expected=[(get(old,a),get(old,b))for i,(a,b)in enumerate(parent['comparisons'])if i not in removed]+combined
 actual=[(get(new,a),get(new,b))for a,b in p['comparisons']]
 need(Counter(expected)==Counter(actual),'every retained and grouped comparison expression')
 common=set(old)&set(new)
 need(all(old[n]==new[n]for n in common),'all unchanged live registers and free ports')
 expected_outputs=set(old[n]for n in old if n not in free)
 expected_outputs|=set(units[name]for group in GROUPS[mode]for name in group)
 for group in GROUPS[mode]:
  v=units[group[0]]
  for name in group[1:]:v=d.op('*',v,units[name]);expected_outputs.add(v)
 need(all(new[n]in expected_outputs for n,_,_,_ in p['source']),'no unexplained live operation')
 for key in('parameters','fixed_numerals','witnesses'):need(exact(p[key],parent[key]),'same complete coordinates '+key)
 if asymmetric:need(p['domains']==parent['domains'],'positive source domains')
 need([r[0]for r in p['source']if 'w'in r[2:]]==['wn2'],'w private to X')
 poly,out=finalizer(p['source'],p['comparisons']);need(poly==p['polynomial_source']and out==p['output'],'literal entire SOS finalizer')
 cert=ledger(p['source'],free,[v for pair in p['comparisons']for v in pair]);full=ledger(poly,free,[out])
 for key in cert:
  if key in p['certificate_ledger']:need(cert[key]==p['certificate_ledger'][key],'full certificate ledger '+key)
 for key in full:
  if key in p['polynomial_ledger']:need(full[key]==p['polynomial_ledger'][key],'full polynomial ledger '+key)
 target={'sos':(75,40,35,13,113,53,60),'pair':(76,41,35,12,111,53,58),'triple':(77,42,35,11,109,53,56),'two_pairs':(77,42,35,11,109,53,56)}[mode]
 need((cert['operations'],cert['M'],cert['A'],len(p['comparisons']),full['operations'],full['M'],full['A'])==target,'all fully paid counts')
 return {'common_registers_and_leaves':len(common),'complete_comparison_expressions':len(actual),'certificate_ledger':cert,'polynomial_ledger':full}

def leading(parent,mode,asymmetric):
 rows=copy.deepcopy(parent['source'])
 if asymmetric:next(r for r in rows if r[0]=='wn2')[-1]='q'
 e={v:(0 if v in CONST else 1,atom(v))for v in parent['polynomial_ledger']['free']}
 def A(x,y,sign=1):
  d=max(x[0],y[0]);return d,add(x[1]if x[0]==d else{},y[1]if y[0]==d else{},sign)
 def M(x,y):return x[0]+y[0],mul(x[1],y[1])
 def G(v):return (0,atom(v))if type(v)is int else e[v]
 for n,o,a,b in rows:e[n]=M(G(a),G(b))if o=='*'else A(G(a),G(b),1 if o=='+'else-1)
 # Guarded main/input graph norm identity (az+v)^2-(a^2+H)z^2.
 def norm(z,v):return A(A(M((0,atom(2)),M(M(G('a'),z),v)),M(v,v)),M(G('a4m5'),M(z,z)),-1)
 units={'first':A(G('tau_square'),G('L9')),'main':norm(G('c'),A(G('wn2'),G('gam'))),'input':norm(G('index_rhs'),A(G('W'),G('modulus_multiple'))),'aux':A(G('L17'),G('aux_y2'))}
 positions={'first':3,'main':7,'input':12,'aux':9};replacement={positions[k]:A(v,(0,atom(1)),-1)for k,v in units.items()}
 # The first residual is1-Nfirst; its sign disappears under squaring.
 removed={positions[k]for group in GROUPS[mode]for k in group};res=[]
 for i,(a,b)in enumerate(parent['comparisons']):
  if i not in removed:res.append(replacement[i]if i in replacement else A(G(a),G(b),-1))
 for group in GROUPS[mode]:
  v=units[group[0]]
  for name in group[1:]:v=M(v,units[name])
  res.append(A(v,(0,atom(1)),-1))
 bound=max(d for d,p in res);top={}
 for d,p in res:
  if d==bound:top=add(top,mul(p,p))
 need(top,'nonzero full leading form')
 # Formal fixed coefficients retained: the displayed full form proves uniformity.
 b,J,w,s,k,g,a,c,delta,i,j=map(atom,('Bm1','Jrep','w','s','k','tau_gap','a','c','delta','i','j'));k=add(atom('eta'),atom('zeta'))
 L=mul(mul(mul(power(b,7 if asymmetric else 9),power(J,7 if asymmetric else 9)),mul(w,power(s,2))),k)
 first=mul(L,add(add(g,g),k,-1));v=add(mul(mul(b,w),J),mul(atom(4),mul(a,atom('ga'))))if asymmetric else None
 main=mul(v,add(mul(atom(2),mul(a,c)),v))if asymmetric else mul(power(b,6),mul(power(w,2),power(J,6)))
 inp=mul(atom(-4),mul(power(a,5),power(delta,2)));aux=mul(power(i,2),mul(power(j,2),power(c,6)))
 if mode=='sos' or mode=='pair'and asymmetric:wanted=mul(first,first)
 elif mode=='pair':wanted=power(mul(main,inp),2)
 elif mode=='triple':wanted=power(mul(mul(main,inp),aux),2)
 else:wanted=power(mul(inp,aux),2)if asymmetric else power(mul(first,main),2)
 need(wanted==top,'closed full homogeneous leader')
 expected={'sos':24 if asymmetric else 28,'pair':24 if asymmetric else 30,'triple':42 if asymmetric else 50,'two_pairs':34 if asymmetric else 44}[mode]
 need(2*bound==expected,'exact complete degree')
 return {'exact_degree':2*bound,'residual_degree_upper_bounds':sorted(d for d,p in res),'full_leading_polynomial':[[list(m),v]for m,v in sorted(top.items())],'unit_degrees':{k:d for k,(d,p)in units.items()}}

def corrections():
 one=atom(1);N={n:atom(n)for n in('first','main','input','aux')};out={}
 for mode in MODES:
  correction={}
  for group in GROUPS[mode]:
   p=one
   for name in group:p=mul(p,N[name])
   r=add(p,one,-1);correction=add(correction,mul(r,r))
   for name in group:r=add(N[name],one,-1);correction=add(correction,mul(r,r),-1)
  out[mode]=[[list(m),v]for m,v in sorted(correction.items())]
 return out

def verify(root,subject):
 for n,h in SUBJECT_PINS.items():need(sha((subject/n).read_bytes())==h,'author pin '+n)
 for n,h in PARENT_PINS.items():need(sha((root/n).read_bytes())==h,'strict inherited source/proof pin '+n)
 receipt=json.loads((subject/'complete113_asymmetric_retained109.json').read_text())
 parent=next(f['packet']for f in json.loads((root/'complete74_gap_selective_projection113.json').read_text())['forms']if f['packet']['eliminated']==['q','C','k','d','kappa','mu'])
 pairs_parent=json.loads((root/'complete113_main_input_units111.json').read_text())['packet']
 path=subject/'complete113_asymmetric_retained109.py';api={'__name__':'_independent_asymmetric109','__file__':str(path)};exec(compile(path.read_bytes(),str(path),'exec'),api)
 need(len(receipt['forms'])==4 and {f['packet']['variant']for f in receipt['forms']}==set(MODES),'exact four forms')
 forms={f['packet']['variant']:f for f in receipt['forms']};rng=random.Random(1093424);counts=Counter();reports=[];corr=corrections()
 def reject(call):
  try:call()
  except ValueError:counts['malformed_rejections']+=1
  else:raise AssertionError('invalid call accepted')
 for mode in MODES:
  p=forms[mode]['packet'];ref=forms[mode]['symmetric_reference'];need(exact(p,api['build'](mode,root=root))and exact(ref,api['symmetric_reference'](mode,root=root)),'entire public child/reference')
  for target,asym in((p,True),(ref,False)):
   proof=structural(parent,target,mode,asym);degree=leading(parent,mode,asym)
   need(target['exact_polynomial_degree']==degree['exact_degree'],'actual target degree')
   counts['complete_literal_circuits']+=1;counts['live_complete_gates']+=len(target['polynomial_source']);counts['full_uniform_leading_forms']+=1;counts['literal_comparisons']+=len(target['comparisons'])
   reports.append({'variant':mode,'asymmetric':asym,'structural':proof,'degree':degree})
  need(ref['all_integer_zero_equivalence']is True,'protected grouping has full integer zero equivalence')
  need('all_integer_zero_equivalence'not in p and 'positive'in p['zero_relation'],'asymmetric coordinate domain remains positive')
  # Independent semantic reconstruction of both comparison metadata maps.
  positions={'first':3,'main':7,'input':12,'aux':9};mapping=[]
  groupnames={'pair':['paired_norm_unit'],'triple':['triple_norm_unit'],'two_pairs':['first_main_unit','input_aux_unit'],'sos':[]}[mode]
  for oi,pair in enumerate(parent['comparisons']):
   group=next((j for j,g in enumerate(GROUPS[mode])if oi in[positions[n]for n in g]),None)
   ni=p['comparisons'].index(pair)if group is None else p['comparisons'].index([groupnames[group],1])
   mapping.append({'parent113_index':oi,'new_index':ni,'role':'same_residual'if group is None else'unit_group_member'})
  need(exact(mapping,p['parent113_comparison_map'])and exact(mapping,ref['parent113_comparison_map']),'all current comparison metadata')
  original=[]
  for x in parent['comparison_map']:
   x=copy.deepcopy(x);idx=x['new_index'];x['role']='historical_positive_definition'if idx is None else mapping[idx]['role']
   if idx is not None:x['new_index']=mapping[idx]['new_index']
   original.append(x)
  need(exact(original,p['original_raw_comparison_map']),'all historical comparison metadata')
  # The sole source mutation, plus a separately expanded w*q^2*q=w*q^3,
  # proves full downstream equality for every value of every coordinate.
  oldrows={r[0]:r for r in ref['source']};newrows={r[0]:r for r in p['source']}
  need(set(oldrows)==set(newrows)and all(oldrows[n]==newrows[n]for n in oldrows if n!='wn2'),'only private X source row changes')
  q,w=atom('q'),atom('w');need(mul(mul(w,power(q,2)),q)==mul(w,power(q,3)),'formal forward scale identity')
  d=DAG()
  def cut(rows):
   e={v:d.a(v)for v in p['polynomial_ledger']['free']}
   for n,o,a,b in rows:e[n]=d.a('proven_X')if n=='wn2'else d.op(o,d.a(a)if type(a)is int else e[a],d.a(b)if type(b)is int else e[b])
   return e
  old,new=cut(ref['polynomial_source']),cut(p['polynomial_source']);need(old==new,'entire polynomial after proved private cut');counts['complete_scale_DAG_identities']+=1;counts['all_cut_registers_and_leaves']+=len(new)
  for case in range(64):
   vals={n:rng.randint(-4,5)if case<32 else rng.randint(1,5)for n in p['polynomial_ledger']['free']}
   if case>=48:vals={n:Fraction(v,3)for n,v in vals.items()};counts['rational_forward_cases']+=1
   if case==0:vals['Bm1']=-1;vals['Jrep']=1
   qv=vals['Bm1']*vals['Jrep']+1;moved=dict(vals);moved['w']*=qv*qv
   left=run(ref['polynomial_source'],vals);right=run(p['polynomial_source'],moved)
   need(all(left[n]==right[n]for n in left if n!='w'),'all computed values under forward scale map')
   counts['whole_forward_identities']+=1;counts['signed_forward_cases']+=case<32
   if qv:
    restored=dict(vals);restored['w']=Fraction(vals['w'])/(qv*qv)
    inverse=run(ref['polynomial_source'],restored);actual=run(p['polynomial_source'],vals)
    need(inverse[ref['output']]==actual[p['output']],'whole rational inverse scale identity');counts['whole_rational_inverse_identities']+=1
   base=run(parent['polynomial_source'],vals)
   units={'first':base['tau_square']+base['L9'],'main':base['L15']-base['Ac2'],'input':base['mu2']-base['scaled_kappa2'],'aux':base['L17']+base['aux_y2']}
   diff=sum(c*prod(units[n]for n in mon)for mon,c in corr[mode])
   need(left[ref['output']]-base[parent['output']]==diff,'entire independently expanded grouping correction');counts['full_grouping_corrections']+=1
   for item in mapping:
    if item['role']=='same_residual':
     oa,ob=parent['comparisons'][item['parent113_index']];na,nb=ref['comparisons'][item['new_index']];get=lambda e,v:v if type(v)is int else e[v]
     need(get(base,oa)-get(base,ob)==get(left,na)-get(left,nb),'every retained residual');counts['retained_residual_values']+=1
   if case in(32,33):
    forward=api['forward_assignment'](p,vals,root=root);need(exact(forward,moved),'public paid-coordinate map');need(exact(api['restore_assignment'](p,forward,root=root),vals),'positive graph inverse');need(api['evaluate'](p,forward,root=root)==left[ref['output']],'public complete value');counts['positive_public_roundtrips']+=1
  for field in p:
   bad=copy.deepcopy(p);del bad[field];reject(lambda bad=bad:api['checked'](bad,root=root))
  for i in range(len(p['polynomial_source'])):
   bad=copy.deepcopy(p);bad['polynomial_source'][i][1]='+'if bad['polynomial_source'][i][1]!='+'else'*';reject(lambda bad=bad:api['checked'](bad,root=root))
  for field in('source','comparisons','witnesses','fixed_numerals'):
   bad=copy.deepcopy(p);bad[field]=tuple(bad[field]);reject(lambda bad=bad:api['checked'](bad,root=root))
  bad=copy.deepcopy(p);bad['exact_polynomial_degree']=float(bad['exact_polynomial_degree']);reject(lambda:api['degree_certificate'](bad,root=root))
  bad=copy.deepcopy(p);bad['parent113_comparison_map'][0]['new_index']=False;reject(lambda:api['checked'](bad,root=root))
  bad=copy.deepcopy(parent if mode=='sos'else pairs_parent);bad['witnesses']=tuple(bad['witnesses']);reject(lambda:api['rewrite'](bad,mode,root=root))
  one={n:1 for n in p['polynomial_ledger']['free']}
  for v in(True,1.0,Fraction(1),0,-1):
   bad=dict(one);bad['x']=v;reject(lambda bad=bad:api['evaluate'](p,bad,root=root))
  reject(lambda:api['restore_assignment'](p,one,root=root));reject(lambda:api['evaluate'](p,one,signed=1,root=root))
  for field in('source','polynomial_source','historical_parent','parent113_comparison_map'):
   fresh=api['build'](mode,root=root);fresh[field].clear();need(exact(api['build'](mode,root=root),p),'public defensive copy');counts['copy_checks']+=1
 # All main/input residue patterns; auxiliary factor uses its actual square t².
 for a in range(4):
  for d0 in range(4):
   for c0 in range(4):need((d0*d0-(a*a+4*a+3)*c0*c0)%4!=3,'main/input -1 exclusion');counts['main_input_mod4_cases']+=1
 for t in range(4):
  for u in range(4):
   for y in range(4):need((t*t*(u*u-y*y)+y*y)%4!=3,'auxiliary -1 exclusion');counts['auxiliary_mod4_cases']+=1
 # Generic unit-factor enumeration mirrors the exact algebraic integer proof:
 # each finite group product1 forces factors±1; every group has at most one
 # unprotected member, hence its protected companions force that member too.
 for mode in MODES:
  for group in GROUPS[mode]:need(sum(n=='first'for n in group)<=1 and len(group)>=2,'at most one unprotected factor per group')
 for variant in(None,True,1,[],{},'bad'):reject(lambda variant=variant:api['build'](variant,root=root))
 # Preserve the relative ../../1980 proof layout and authenticate actual bad
 # files in preference to any correct basename/sibling fallbacks.
 with tempfile.TemporaryDirectory(prefix='review-asymmetric109-')as tmp:
  dest=Path(tmp)/'Papers'/'research-wip'/'native-stream-queue';dest.mkdir(parents=True)
  for name in PARENT_PINS:
   path2=dest/name;path2.parent.mkdir(parents=True,exist_ok=True);path2.write_bytes((root/name).read_bytes())
  api['build'](root=dest)
  for name in PARENT_PINS:
   path2=dest/name;raw=path2.read_bytes();path2.write_bytes(raw+b'\n')
   if '/'in name:(dest/Path(name).name).write_bytes(raw)
   reject(lambda:api['build'](root=dest));path2.write_bytes(raw);counts['strict_warm_pin_rejections']+=1
   if '/'in name:counts['relative_proof_mismatch_rejections']+=1
 proc=subprocess.run([sys.executable,'-O',str(path),'--root',str(root)],capture_output=True,text=True,timeout=30);need(proc.returncode and 'without -O'in proc.stderr,'optimized mode rejection');counts['optimized_rejections']+=1
 old=json.loads((root/'complete86_first_root_partitions.json').read_text())['census']['combined_frontier']
 previous=[(p['operations'],p['exact_degree'])for p in old]+[(113,28),(111,30)]
 current=[(f['packet']['polynomial_ledger']['operations'],f['packet']['exact_polynomial_degree'])for f in forms.values()]
 def frontier(points):return sorted({p for p in points if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in points)})
 need([list(p)for p in frontier(current)]==receipt['family_frontier'],'measured four-form frontier')
 need([list(p)for p in frontier(previous+current)]==receipt['known_union_frontier'],'authenticated previous frontier union')
 return {'status':'PASS_INDEPENDENT_ASYMMETRIC_RETAINED109','review_source_sha256':sha(Path(__file__).read_bytes()),'subject_pins':SUBJECT_PINS,'parent_pins':PARENT_PINS,'counts':dict(counts),'forms':reports,'grouping_corrections':corr,'family_frontier':[list(p)for p in frontier(current)],'known_union_frontier':[list(p)for p in frontier(previous+current)],'scope':'Eight complete emitted asymmetric/symmetric circuits, all source rows and finalizers, rational scale identities, exact uniform leaders, integer grouping theorem and bounded API/pin/copy tests. Asymmetric integer inverse uses the separately reviewed positive bootstrap theorem; no full universal positive zero materialized.'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--subject-root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root,v.subject_root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
