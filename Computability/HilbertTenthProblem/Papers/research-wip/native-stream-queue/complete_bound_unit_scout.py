#!/usr/bin/env python3
"""Bounded six-unit scout on the complete asymmetric retained-a,c source.

Separate integer and positive-only partition families are recorded.
This is not a maintained public compiler or an unrestricted partition census.
"""
import argparse,copy,hashlib,itertools,json,random,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'complete109_index_unit_tradeoffs107.py':'d255896294684f8d6411d992f5f0ba60a7f4051aa841d7e325f5347d64c23600',
'complete109_index_unit_tradeoffs107.json':'3d8d8d473cc866ebd585ac5605648839cfe014e98b5be2a10938cc0dfcfe12b3',
'complete109_index_unit_tradeoffs107.md':'928f760d73a7da081eace63cfcb144f41cd4271fcd92fbc3860d482738b16b9b'}
NAMES=['first','main','input','auxiliary','index','bound']
PORTS=['first_unit','main_unit','input_unit','aux_unit','index_unit','bound_unit']
OLD=[3,7,12,9,5,0]
DEGREES=[12,4,7,10,7,1]
UNPROTECTED={0,4,5}
TARGETS={'108_degree30':[[0],[4,2],[5,1,3]],'110_degree24':[[0],[4,1],[5,2],[3]]}
POSITIVE_TARGETS={'106_degree42_positive':[[4,1,3],[5,0,2]],'108_degree28_positive':[[5,0],[1,3],[4,2]]}

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(x):return hashlib.sha256(x).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def add(a,b,s=1):
 d=dict(a)
 for m,c in b.items():d[m]=d.get(m,0)+s*c
 return {m:c for m,c in d.items()if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   v=tuple(x+y for x,y in zip(m,n));d[v]=d.get(v,0)+c*e
 return {m:c for m,c in d.items()if c}
def powp(p,n,one):
 r=one
 for _ in range(n):r=mul(r,p)
 return r
def expand(rows,free):
 zero=(0,)*len(free)
 atom=lambda c:{zero:c}if c else{}
 d={v:{tuple(int(i==j)for i in range(len(free))):1}for j,v in enumerate(free)}
 for n,op,a,b in rows:
  a=atom(a)if type(a)is int else d[a];b=atom(b)if type(b)is int else d[b]
  d[n]=mul(a,b)if op=='*'else add(a,b,-1 if op=='-'else 1)
 return d,atom

def evaluate(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else d[a];b=b if type(b)is int else d[b]
  d[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return d

def finalizer(rows,pairs):
 rows=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):rows += [[f'new_r{i}','-',a,b],[f'new_s{i}','*',f'new_r{i}',f'new_r{i}']]
 out='new_s0'
 for i in range(1,len(pairs)):
  name=f'new_sum{i}';rows.append([name,'+',out,f'new_s{i}']);out=name
 return rows,out

def ledger(rows,free,outputs,fixed):
 seen=set(free);deps={};ds={v:int(v not in fixed)for v in free};M=0
 for n,op,a,b in rows:
  need(type(n)is str and n not in seen and type(op)is str and op in('+','-','*'),'typed unique row')
  need(all(type(v)is int or type(v)is str and v in seen for v in(a,b)),'closed exact operands')
  da=0 if type(a)is int else ds[a];db=0 if type(b)is int else ds[b];ds[n]=da+db if op=='*'else max(da,db)
  seen.add(n);deps[n]=(a,b);M+=op=='*'
 live=set();stack=list(outputs)
 while stack:
  n=stack.pop()
  if type(n)is str and n not in live:live.add(n);stack.extend(deps.get(n,()))
 need(set(deps)<=live and set(free)<=live,'all paid gates and supplied fields live')
 return dict(operations=len(rows),M=M,A=len(rows)-M,all_gates_live=True,literal_degree_upper_bound=max(ds[n]if type(n)is str else 0 for n in outputs))

def all_partitions(seq):
 if not seq:yield [];return
 for p in all_partitions(seq[1:]):
  yield [[seq[0]]]+p
  for i in range(len(p)):yield p[:i]+[[seq[0]]+p[i]]+p[i+1:]
def canonical_partition(p):return sorted([sorted(g)for g in p],key=lambda g:g[0])

def unit_core(p):
 pairs=p['comparisons'];by={r[0]:r for r in p['source']}
 need(pairs[0]==['raw_bound','q']and by['q']==['q','+','repunit',1]and by['repunit']==['repunit','*','Bm1','Jrep'],'actual bound and q definition')
 need(by['raw_bound']==['raw_bound','+','bounded','scaled_t']and by['bounded']==['bounded','+','marked_rhs','alpha'],'actual full bound cone')
 need(any('q'in r[2:]for r in p['source']if r[0]!='q'),'q retained because other consumers exist')
 need(by['r1']==['r1','+','r',1]and by['R11']==['R11','+','r1','hpm1'],'actual index cone')
 need([r[0]for r in p['source']if 'r1'in r[2:]]==['R11'],'private r1')
 for name in('R11','R9','R15','P17','norm_rhs'):need(not any(name in r[2:]for r in p['source'])and sum(name in pair for pair in pairs)==1,'private replaced comparison side')
 need([pairs[i]for i in OLD]==[['R9','L9'],['L15','R15'],['mu2','norm_rhs'],['L17','P17'],['R10b','R11'],['raw_bound','q']],'literal six comparison interfaces')
 rows=[]
 for n,op,a,b in p['source']:
  if n=='R9':continue
  if n=='R15':n,op,a,b='main_unit','-','L15','Ac2'
  elif n=='norm_rhs':n,op,a,b='input_unit','-','mu2','scaled_kappa2'
  elif n=='P17':n,op,a,b='aux_unit','+','L17','aux_y2'
  elif n=='r1':n,op,a,b='index_partial','-','R10b','r'
  elif n=='R11':n,op,a,b='index_unit','-','index_partial','hpm1'
  rows.append([n,op,a,b])
  if n=='repunit':rows.append(['bound_unit','-','raw_bound','repunit'])
  if n=='L9':rows.append(['first_unit','+','tau_square','L9'])
 need(len(rows)==76 and sum(r[1]=='*'for r in rows)==40,'76-gate fully paid unit core')
 return rows

def candidate(p,core,groups,positive_only=False):
 unprotected={4,5}if positive_only else UNPROTECTED
 need(type(positive_only)is bool and sorted(i for g in groups for i in g)==list(range(6))and all(len(set(g)&unprotected)<=1 for g in groups),'exact permitted partition')
 rows=copy.deepcopy(core);pairs=[];mapping=[None]*len(p['comparisons'])
 for i,pair in enumerate(p['comparisons']):
  if i not in OLD:mapping[i]=dict(parent_index=i,new_index=len(pairs),role='unchanged');pairs.append(copy.deepcopy(pair))
 metas=[]
 for gi,g in enumerate(groups):
  port=PORTS[g[0]]
  for j,k in enumerate(g[1:]):
   n=f'bound_product{gi}_{j}';rows.append([n,'*',port,PORTS[k]]);port=n
  index=len(pairs);pairs.append([port,1]);metas.append(dict(unit_indices=g,ports=[PORTS[i]for i in g],port=port,comparison_index=index))
  for k in g:mapping[OLD[k]]=dict(parent_index=OLD[k],new_index=index,role='unit_group',unit=NAMES[k],old_residual_sign=-1 if k==0 else 1)
 poly,out=finalizer(rows,pairs);free=p['polynomial_ledger']['free'];fixed=p['fixed_numerals'];L=ledger(poly,free,[out],fixed);C=ledger(rows,free,[v for pair in pairs for v in pair],fixed);g=len(groups)
 need((L['operations'],L['M'],L['A'],len(pairs))==(102+2*g,53,49+2*g,7+g),'complete paid group formula')
 return dict(source=rows,comparisons=pairs,polynomial_source=poly,output=out,certificate_ledger=C,polynomial_ledger=dict(L,free=free),parameters=p['parameters'],fixed_numerals=fixed,witnesses=p['witnesses'],unit_groups=metas,parent_comparison_map=mapping,exact_polynomial_degree=2*max(sum(DEGREES[i]for i in group)for group in groups),positive_only=positive_only,domain=('Same strictly positive zero set on the admissible fixed-program slice as the authenticated asymmetric113 parent; no signed-integer equivalence asserted.'if positive_only else'Same entire integer zero set as the authenticated asymmetric113 parent. Universal semantics require its positive compiled input slice.'),scope='Bounded source scout; fixed supplied ports and24 witnesses unchanged; no general public compiler or unrestricted grouping claim.')

def correction(groups):
 d,co=expand([],NAMES);old={};new={}
 for name in NAMES:old=add(old,mul(add(d[name],co(1),-1),add(d[name],co(1),-1)))
 for g in groups:
  product=co(1)
  for i in g:product=mul(product,d[NAMES[i]])
  residual=add(product,co(1),-1);new=add(new,mul(residual,residual))
 return add(new,old,-1)

def verify(root):
 blobs={}
 for name,pin in PINS.items():
  data=(root/name).read_bytes();need(sha(data)==pin,'frozen direct parent '+name);blobs[name]=data
 name='complete109_index_unit_tradeoffs107.py';m=types.ModuleType('_pinned_index_scout');m.__file__=str(root/name);exec(compile(blobs[name],str(root/name),'exec'),m.__dict__)
 authenticated=m.authenticated(root);receipt=json.loads(blobs['complete109_index_unit_tradeoffs107.json']);p=m.canonical_parent(root=root);need(exact(p,receipt['canonical_parent']),'selected complete canonical113 source')
 core=unit_core(p);free=p['polynomial_ledger']['free'];fixed=p['fixed_numerals'];env,co=expand(core,free);oldenv,_=expand(p['source'],free);weights=[int(v not in fixed)for v in free]
 degree=lambda f:max((sum(x*w for x,w in zip(mon,weights))for mon in f),default=-1)
 top=lambda f:{mon:c for mon,c in f.items()if sum(x*w for x,w in zip(mon,weights))==degree(f)}
 one=co(1)
 def product(*polys):
  r=one
  for f in polys:r=mul(r,f)
  return r
 power=lambda f,n:powp(f,n,one)
 b,J=env['Bm1'],env['Jrep'];k=add(env['eta'],env['zeta']);Dtop=add(product(b,env['w'],J),product(co(4),env['ga'],env['a']));Mtop=add(power(Dtop,2),product(co(2),env['a'],env['c'],Dtop))
 Btop=add(add(add(add(env['Z'],env['W']),env['alpha']),product(env['twice_cell_bits'],env['x'])),product(b,J),-1)
 leaders=[product(power(b,7),env['w'],power(env['s'],2),k,power(J,7),add(product(co(2),env['tau_gap']),k,-1)),Mtop,product(co(-4),power(env['delta'],2),power(env['a'],5)),product(power(env['i'],2),power(env['j'],2),power(env['c'],6)),product(co(-1),env['h'],env['w'],env['s'],power(b,4),power(J,4)),Btop]
 for name,n,lead in zip(PORTS,DEGREES,leaders):need(degree(env[name])==n and top(env[name])==lead,'actual uniform leading polynomial '+name)
 ordinary=[]
 for i,(a,b)in enumerate(p['comparisons']):
  aa=co(a)if type(a)is int else oldenv[a];bb=co(b)if type(b)is int else oldenv[b];res=add(aa,bb,-1)
  if i in OLD:
   k=OLD.index(i);unit=add(env[PORTS[k]],co(1),-1);need(res==({mon:-c for mon,c in unit.items()}if k==0 else unit),'literal old residual equals oriented unit residual')
  else:
   aa=co(a)if type(a)is int else env[a];bb=co(b)if type(b)is int else env[b];need(res==add(aa,bb,-1),'retained entire residual coefficient identity');ordinary.append(degree(res))
 need(max(ordinary)<=6,'all seven retained rows below unit group degree')
 partitions=list(all_partitions(list(range(6))));need(len(partitions)==203,'all six-label partitions')
 allowed=[canonical_partition(p)for p in partitions if all(len(set(g)&UNPROTECTED)<=1 for g in p)]
 need(len({json.dumps(x)for x in allowed})==len(allowed)==77,'exact restricted partition census')
 census=[]
 for part in sorted(allowed,key=lambda g:(len(g),g)):
  packet=candidate(p,core,part);census.append(dict(partition=[[NAMES[i]for i in group]for group in part],operations=packet['polynomial_ledger']['operations'],M=packet['polynomial_ledger']['M'],A=packet['polynomial_ledger']['A'],equations=len(packet['comparisons']),witnesses=len(packet['witnesses']),exact_degree=packet['exact_polynomial_degree'],source_sha256=sha(json.dumps(packet,sort_keys=True,separators=(',',':')).encode())))
 frequencies=dict(sorted(Counter(len(part)for part in allowed).items()));need(frequencies=={3:27,4:37,5:12,6:1},'group counts')
 frontier=sorted({(r['operations'],r['exact_degree'])for r in census if not any(s['operations']<=r['operations']and s['exact_degree']<=r['exact_degree']and(s['operations'],s['exact_degree'])!=(r['operations'],r['exact_degree'])for s in census)})
 need(frontier==[(108,30),(110,24)],'restricted family Pareto frontier')
 positive_allowed=[canonical_partition(g)for g in partitions if all(not(4 in block and 5 in block)for block in g)]
 need(len({json.dumps(g)for g in positive_allowed})==len(positive_allowed)==151,'positive-only partition census')
 positive_frequencies=dict(sorted(Counter(len(g)for g in positive_allowed).items()));need(positive_frequencies=={2:16,3:65,4:55,5:14,6:1},'positive-only group counts')
 positive_census=[]
 for part in sorted(positive_allowed,key=lambda g:(len(g),g)):
  packet=candidate(p,core,part,True);positive_census.append(dict(partition=[[NAMES[i]for i in group]for group in part],operations=packet['polynomial_ledger']['operations'],M=packet['polynomial_ledger']['M'],A=packet['polynomial_ledger']['A'],equations=len(packet['comparisons']),witnesses=len(packet['witnesses']),exact_degree=packet['exact_polynomial_degree'],source_sha256=sha(json.dumps(packet,sort_keys=True,separators=(',',':')).encode())))
 positive_frontier=sorted({(r['operations'],r['exact_degree'])for r in positive_census if not any(t['operations']<=r['operations']and t['exact_degree']<=r['exact_degree']and(t['operations'],t['exact_degree'])!=(r['operations'],r['exact_degree'])for t in positive_census)})
 need(positive_frontier==[(106,42),(108,28),(110,24)],'positive-only frontier')
 # Authenticate the exact published independent sign observation; symbolic
 # norm preservation below does not import any native conclusion.
 sign_note=authenticated['complete113_asymmetric_retained109.md'].decode()
 need("k'=(2V+1)k-2T, T'=(2V+1)T-2V(V+1)k"in sign_note,'pinned sign proof anchor')
 descent,ct=expand([],['V','T','k']);V,T,K=[descent[n]for n in('V','T','k')];DD=mul(V,add(V,ct(1)));AA=add(mul(ct(2),V),ct(1));Knext=add(mul(AA,K),mul(ct(2),T),-1);Tnext=add(mul(AA,T),mul(mul(ct(2),DD),K),-1)
 norm=add(mul(T,T),mul(DD,mul(K,K)),-1);norm_next=add(mul(Tnext,Tnext),mul(DD,mul(Knext,Knext)),-1);need(norm==norm_next,'exact descent norm identity')
 signed_example={v:1 for v in free};signed_example.update(Jrep=0,tau_gap=0,zeta=0);actual=evaluate(core,signed_example);need(actual['first_unit']==-1,'first norm is not protected on all integer tuples')
 rng=random.Random(1083024);forms=[];counts=dict(emitted_integer_census_schedules=77,emitted_positive_census_schedules=151,actual_unit_residual_identities=6,retained_residual_identities=7,whole_corrections=0,signed_cases=0,rational_cases=0,individual_residual_values=0)
 for name,groups in (TARGETS|POSITIVE_TARGETS).items():
  positive_only=name in POSITIVE_TARGETS
  c=candidate(p,core,groups,positive_only);d,_=expand(c['source'],free);degrees=[];group_leaders=[]
  for a,b in c['comparisons']:
   res=add(co(a)if type(a)is int else d[a],co(b)if type(b)is int else d[b],-1);degrees.append(degree(res))
  topD=max(degrees);maxima=[i for i,v in enumerate(degrees)if v==topD];need(len(maxima)==(2 if name=='108_degree28_positive'else 1),'complete maximal residual multiplicity')
  for meta in c['unit_groups']:
   lead=product(*(leaders[i]for i in meta['unit_indices']));need(top(d[meta['port']])==lead,'actual group coefficient leader');group_leaders.append(lead)
  lead={}
  for ix in maxima:lead=add(lead,power(top(d[c['comparisons'][ix][0]]),2))
  if name=='108_degree30':expected=power(product(Btop,Mtop,leaders[3]),2)
  elif name=='110_degree24':expected=power(leaders[0],2)
  elif name=='106_degree42_positive':expected=power(product(leaders[4],Mtop,leaders[3]),2)
  else:expected=add(power(product(Mtop,leaders[3]),2),power(product(leaders[4],leaders[2]),2))
  need(lead==expected and c['exact_polynomial_degree']==2*topD,'full uniform exact degree and leading coefficients')
  diff=correction(groups)
  for case in range(48):
   values={v:rng.randint(-3,4)if case<24 else rng.randint(1,4)for v in free};values.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   if case>=40:values={v:Fraction(x,2)if v not in fixed else x for v,x in values.items()}
   old=evaluate(p['polynomial_source'],values);new=evaluate(c['polynomial_source'],values);u=[new[v]for v in PORTS];delta=0
   for mon,coef in diff.items():
    for value,e in zip(u,mon):coef*=value**e
    delta+=coef
   need(new[c['output']]-old[p['output']]==delta,'complete all-value polynomial correction')
   for entry in c['parent_comparison_map']:
    i=entry['parent_index'];a,b=p['comparisons'][i];oldr=(a if type(a)is int else old[a])-(b if type(b)is int else old[b])
    if entry['role']=='unchanged':
     a,b=c['comparisons'][entry['new_index']];want=(a if type(a)is int else new[a])-(b if type(b)is int else new[b])
    else:want=entry['old_residual_sign']*(new[PORTS[NAMES.index(entry['unit'])]]-1)
    need(oldr==want,'all actual residual maps');counts['individual_residual_values']+=1
   counts['whole_corrections']+=1;counts['signed_cases']+=case<24;counts['rational_cases']+=case>=40
  forms.append(dict(name=name,packet=c,full_correction=dict(unit_order=NAMES,coefficients=[[list(k),v]for k,v in sorted(diff.items())]),degree_proof=dict(unit_degrees=DEGREES,residual_degrees=degrees,leading_residual_indices=maxima,exact_degree=2*topD,variables=free,weights=weights,highest_polynomial=[[list(k),v]for k,v in sorted(lead.items())],uniformity='Closed actual coefficient leaders are nonzero on every fixed Bm1>0 slice; bound leader has alpha coefficient1. Other compiled numerals cannot cancel these leaders.')))
 signs=0
 for a,x,y in itertools.product(range(4),repeat=3):need((x*x-(a*a+4*a+3)*y*y)%4!=3,'main/input exclude minus1');signs+=1
 for t,H,y in itertools.product(range(4),repeat=3):need((t*t*(H*H-y*y)+y*y)%4!=3,'aux excludes minus1');signs+=1
 factorcases=0
 for values in itertools.product(range(-2,3),repeat=6):
  if any(values[i]==-1 for i in(1,2,3)):continue
  expected=all(v==1 for v in values)
  for groups in TARGETS.values():
   okay=True
   for group in groups:
    z=1
    for i in group:z*=values[i]
    okay=okay and z==1
   need(okay==expected,'bounded admissible integer product regression');factorcases+=1
 positive_factorcases=0
 for values in itertools.product(range(-2,3),repeat=6):
  if any(values[i]==-1 for i in(0,1,2,3)):continue
  expected=all(v==1 for v in values)
  for groups in POSITIVE_TARGETS.values():
   okay=True
   for group in groups:
    z=1
    for i in group:z*=values[i]
    okay=okay and z==1
   need(okay==expected,'bounded positive-protected product regression');positive_factorcases+=1
 counts.update(mod4_cases=signs,integer_factor_cases=factorcases,positive_protected_factor_cases=positive_factorcases,descent_norm_identities=1,first_norm_signed_negative_examples=1)
 previous=[tuple(x)for x in receipt['known_union_frontier']];points=previous+frontier+positive_frontier;combined=sorted({p for p in points if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in points)})
 return dict(status='PASS_BOUNDED_SIX_UNIT_SCOUT',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,transitive_pins=m.PINS,canonical_parent=p,unit_core=core,unit_order=NAMES,unit_degrees=DEGREES,unit_highest_polynomials=[[[list(k),v]for k,v in sorted(f.items())]for f in leaders],retained_residual_degrees=ordinary,counts=counts,census=census,group_counts={str(k):v for k,v in frequencies.items()},family_frontier=[list(x)for x in frontier],positive_census=positive_census,positive_group_counts={str(k):v for k,v in positive_frequencies.items()},positive_family_frontier=[list(x)for x in positive_frontier],positive_descent={'pinned_note':'complete113_asymmetric_retained109.md','norm_identity':'Tnext^2-V(V+1)Knext^2=T^2-V(V+1)K^2','signed_first_norm_minus_one_assignment':signed_example,'scope':'V>1 and T,k positive; minimal k descent. Actual positive source has q>=2 and V=w*s^2*q^7>1 before any equation.'},comparison_catalogue='Frozen index-unit receipt only; parallel or later censuses not incorporated.',previous_frontier=[list(x)for x in previous],union_frontier=[list(x)for x in combined],forms=forms,scope='Separate77 all-integer partitions and151 positive-only partitions of the six actual unit factors; exact paid source censuses and four complete candidate sources. Positive-only family uses pinned first-norm descent. No unrestricted grouping or global optimality claim.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['family_frontier'],r['positive_family_frontier'],r['counts'])
if __name__=='__main__':main()
