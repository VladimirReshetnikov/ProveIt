#!/usr/bin/env python3
"""Independent literal-source/leading-form audit of selective positive graph SOS."""
import argparse,copy,hashlib,itertools,json,random,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
SUBJECT_PINS={'complete74_gap_selective_projection113.py': '573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4', 'complete74_gap_selective_projection113.json': '2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3', 'complete74_gap_selective_projection113.md': '3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa'}
PARENT_PINS={'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_positive_elimination.json': '03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703', 'complete75_positive_elimination.md': '59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b', 'complete75_positive_root89.py': 'f850ee8cd5e00b9235a8f192d2f95f6b27cf72a40c3f6b6e3fa054700d793c72', 'complete75_positive_root89.md': '7b85195a800b909e3bf6e55fa85decfaa08299cf1e100efa866659571d192085', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5'}
CONST=('Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF')
DEFS={'q':('q',0),'C':('marked_rhs',4),'k':('R10b',7),'a':('R12',9),'c':('R10a',6),'d':('R14',10),'kappa':('index_rhs',15),'mu':('exponent_rhs',18)}
DEFAULT=('q','C','k','d','kappa','mu')
def need(x,m):
 if not x:raise AssertionError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def canonical(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(same(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b
def plus(a,b,s=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+s*v
 return {m:v for m,v in c.items() if v}
def times(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():q=tuple(sorted(m+n));c[q]=c.get(q,0)+v*w
 return {m:v for m,v in c.items() if v}
def atom(v):return {():v} if type(v)is int else {(v,):1}
def source_values(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  a=a if type(a)is int else e[a];b=b if type(b)is int else e[b];e[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return e

def ledger(rows,ports):
 names={r[0] for r in rows};free={x for r in rows for x in r[2:] if type(x)is str and x not in names};seen=set(free);d={}
 need(len(names)==len(rows),'duplicate node')
 for n,o,a,b in rows:
  need(type(n)is str and n not in seen and o in ('+','-','*'),'exact node')
  need(all(type(x)is int or type(x)is str and x in seen for x in (a,b)),'closed exact operand')
  seen.add(n);d[n]=(a,b)
 live=set();todo=list(ports)
 while todo:
  v=todo.pop()
  if type(v)is int or v in free or v in live:continue
  need(v in d,'missing terminal');live.add(v);todo.extend(d[v])
 need(live==names,'all gates live');ops=Counter(r[1] for r in rows)
 return {'operations':len(rows),'M':ops['*'],'A':ops['+']+ops['-'],'all_gates_live':True,'free':sorted(free)}

def local_identity():
 L,g,k,a,z,v,H=map(atom,('L','g','k','a','z','v','H'))
 old=plus(times(L,plus(L,k)),plus(times(plus(L,g),plus(L,g)),atom(1),-1),-1)
 new=plus(plus(atom(1),times(g,g),-1),times(L,plus(plus(g,g),k,-1)),-1)
 need(old==new,'full first residual identity')
 root=plus(times(a,z),v);left=plus(plus(times(root,root),times(plus(times(a,a),H),times(z,z)),-1),atom(1),-1)
 right=plus(plus(plus(times(atom(2),times(times(a,z),v)),times(v,v)),times(H,times(z,z)),-1),atom(1),-1)
 need(left==right,'norm cancellation identity')
 return {'first_residual':[[list(m),c] for m,c in sorted(old.items())],'norm_cancellation':[[list(m),c] for m,c in sorted(left.items())]}

def check_literal(parent,p):
 chosen=tuple(p['eliminated']);need(chosen==tuple(v for v in DEFS if v in chosen),'ordered exact subset')
 aliases={v:DEFS[v][0] for v in chosen if v!='q'}
 if 'q' in chosen:aliases['qm1']='repunit'
 nodes={n:[o,a,b] for n,o,a,b in parent['source']}
 need(nodes['ksn2']==['*','k','sn2'] and nodes['first_next']==['+','first_root_base','k'],'supplied raw k')
 nodes.pop('first_next');nodes.update({'tau_square':['*','tau_gap','tau_gap'],'R9':['-',1,'tau_square'],'twice_tau_gap':['+','tau_gap','tau_gap'],'first_signed_gap':['-','twice_tau_gap','k'],'L9':['*','first_root_base','first_signed_gap']})
 if 'q' in chosen:nodes.pop('qm1');nodes['q']=['+','repunit',1]
 expected={n:[o,aliases.get(a,a),aliases.get(b,b)] for n,(o,a,b) in nodes.items()}
 actual={n:[o,a,b] for n,o,a,b in p['source']};need(same(actual,expected),'every actual changed/unchanged source row')
 omitted={DEFS[v][1] for v in chosen};indices=[i for i in range(19) if i not in omitted]
 pairs=[]
 for i,(a,b) in enumerate(parent['comparisons']):
  if i in omitted:continue
  a,b=aliases.get(a,a),aliases.get(b,b)
  pairs.append([b,a] if i==5 else [a,b])
 need(p['comparisons']==pairs and p['retained_original_comparison_indices']==indices,'all comparison rows')
 mapping=[{'old_index':i,'new_index':indices.index(i)if i in indices else None,'deleted_definition':next((v for v in chosen if DEFS[v][1]==i),None)}for i in range(19)]
 need(same(mapping,p['comparison_map']),'full current comparison map')
 witnesses=[v if v!='tau' else 'tau_gap' for v in parent['witnesses'] if v not in chosen]
 need(p['witnesses']==witnesses and p['parameters']==['x'] and p['fixed_numerals']==list(CONST),'complete interface')
 need(p['restoration_registers']=={v:DEFS[v][0] for v in chosen},'actual restoration ports')
 out=copy.deepcopy(p['source'])
 for j,(a,b) in enumerate(pairs):out.extend([[f'residual_{j}','-',a,b],[f'square_{j}','*',f'residual_{j}',f'residual_{j}']])
 last='square_0'
 for j in range(1,len(pairs)):
  n=f'sum_{j}';out.append([n,'+',last,f'square_{j}']);last=n
 need(out==p['polynomial_source'] and last==p['output'],'entire literal SOS finalizer')
 cert=ledger(p['source'],[v for pair in pairs for v in pair]);full=ledger(out,[last]);need(cert==p['certificate_ledger'] and full==p['polynomial_ledger'],'actual complete ledgers')
 need((cert['operations'],cert['M'],cert['A'])==(75,40,35),'75 complete source')
 need(full['operations']==131-3*len(chosen) and full['M']==59-len(chosen) and full['A']==72-2*len(chosen),'complete residual/finalizer charge')
 need(set(full['free'])==set(witnesses)|set(CONST)|{'x'},'exact free coordinates')
 return cert,full

def leading_proof(p):
 # Coefficients retain ALL formal fixed numerals, rather than substituting
 # a single compiler. Monomials below represent actual leading polynomials.
 env={v:(0 if v in CONST else 1,atom(v)) for v in p['polynomial_ledger']['free']}
 def add(a,b,s=1):
  d=max(a[0],b[0]);return d,plus(a[1] if a[0]==d else {},b[1] if b[0]==d else {},s)
 def mul(a,b):return a[0]+b[0],times(a[1],b[1])
 def get(x):return (0,atom(x)) if type(x)is int else env[x]
 for n,op,a,b in p['source']:env[n]=mul(get(a),get(b)) if op=='*' else add(get(a),get(b),1 if op=='+' else -1)
 alias=lambda n:p['restoration_registers'].get(n,n)
 residuals=[]
 for old_index,(left,right) in zip(p['retained_original_comparison_indices'],p['comparisons']):
  if old_index==11 and 'd' in p['eliminated']:z=get(alias('c'));extra=add(get('wn2'),get('gam'))
  elif old_index==17 and 'mu' in p['eliminated']:z=get(alias('kappa'));extra=add(get('W'),get('modulus_multiple'))
  else:residuals.append(add(get(left),get(right),-1));continue
  azv=mul(mul(get(alias('a')),z),extra)
  residuals.append(add(add(add(mul((0,atom(2)),azv),mul(extra,extra)),mul(get('a4m5'),mul(z,z)),-1),(0,atom(1)),-1))
 bound=max(d for d,p in residuals);top={}
 for d,r in residuals:
  if d==bound:top=plus(top,times(r,r))
 need(bool(top),'nonzero complete top polynomial')
 # A top specialization in ordinary coordinates, with Bm1 still indeterminate,
 # proves nonvanishing for EVERY positive Bm1. Other fixed numerals are absent.
 leaders=[]
 for j,(d,r) in enumerate(residuals):
  if d!=bound:continue
  need(not any(set(m)&(set(CONST)-{'Bm1'}) for m in r),'uniform other-fixed-parameter independence')
  coeff={}
  for monomial,c in r.items():
   e=monomial.count('Bm1');c*=3**monomial.count('tau_gap');coeff[e]=coeff.get(e,0)+c
  coeff={e:c for e,c in coeff.items() if c}
  if coeff and (all(c>0 for c in coeff.values()) or all(c<0 for c in coeff.values())):leaders.append({'old_index':p['retained_original_comparison_indices'][j],'coefficients':[[e,c] for e,c in sorted(coeff.items())]})
 need(bool(leaders),'uniform sign definite attaining specialization')
 need([d for d,r in residuals]==p['residual_degree_bounds'] and 2*bound==p['exact_polynomial_degree']==p['polynomial_degree_upper_bound'],'all degree metadata')
 return {'exact_degree':2*bound,'residual_bounds':[d for d,r in residuals],'attaining_residuals':leaders,'full_leading_polynomial':[[list(m),c] for m,c in sorted(top.items())]}

def verify(root,subject):
 for n,h in SUBJECT_PINS.items():need(sha((subject/n).read_bytes())==h,'subject pin '+n)
 for n,h in PARENT_PINS.items():need(sha((root/n).read_bytes())==h,'parent pin '+n)
 r=json.loads((subject/'complete74_gap_selective_projection113.json').read_text());parent=json.loads((root/'complete74_factored_first_norm.json').read_text())['forms'][0]['packet']
 path=subject/'complete74_gap_selective_projection113.py';api={'__name__':'_independent_113','__file__':str(path)};exec(compile(path.read_bytes(),str(path),'exec'),api)
 symbolic=local_identity();counts=Counter();records=[];rng=random.Random(11328);default_degree=None
 packets={tuple(f['packet']['eliminated']):f['packet'] for f in r['forms']};selections=[tuple(v for v,b in zip(DEFS,bs) if b) for bs in itertools.product((False,True),repeat=8)]
 need(set(packets)==set(selections) and len(r['forms'])==256,'all256 exactly once')
 for ix,selected in enumerate(selections):
  p=packets[selected];cert,full=check_literal(parent,p);degree=leading_proof(p);counts['literal_complete_sources']+=1;counts['actual_source_rows']+=len(p['source']);counts['uniform_full_leading_certificates']+=1;counts['live_complete_gates']+=len(p['polynomial_source'])
  if selected==DEFAULT:
   default_degree=degree
   # Independent closed form for the complete degree28 leader.
   b,J,w,s,e,z,g=map(atom,('Bm1','Jrep','w','s','eta','zeta','tau_gap'));power=lambda p,n:__import__('functools').reduce(times,[p]*n,atom(1))
   Ltop=times(times(times(power(b,9),power(J,9)),times(w,power(s,2))),plus(e,z));first=times(Ltop,plus(plus(g,g),plus(e,z),-1));wanted=times(first,first)
   need(wanted=={tuple(m):c for m,c in degree['full_leading_polynomial']},'entire default leading polynomial')
  for case in range(4):
   values={v:rng.randint(1,5) if case==0 else rng.randint(-4,5) for v in full['free']}
   if case==3:values={v:Fraction(a,3) for v,a in values.items()};counts['rational_graph_cases']+=1
   new=source_values(p['polynomial_source'],values);lift={v:values[v] for v in parent['polynomial_ledger']['free'] if v in values}
   lift.update({v:new[name] for v,name in p['restoration_registers'].items()});lift['tau']=new['first_root_base']+values['tau_gap'];old=source_values(parent['polynomial_source'],lift)
   need(new[p['output']]==old[parent['output']],'entire full graph identity')
   for oi,(a,b) in enumerate(parent['comparisons']):
    d=old[a]-old[b]
    if oi in p['retained_original_comparison_indices']:
     j=p['retained_original_comparison_indices'].index(oi);aa,bb=p['comparisons'][j];need(d==new[aa]-new[bb],'individual exact residual')
    else:need(d==0,'deleted graph row')
    counts['exact_graph_residuals']+=1
   if case==0:need(all(v>0 for v in lift.values()),'unconditional positive restoration');counts['positive_graph_lifts']+=1
   counts['whole_graph_cases']+=1
  if ix%32==0 or selected==DEFAULT:
   need(same(api['build'](selected,root=root),p) and same(api['checked'](p,root=root),p),'public complete canonical packet');counts['public_packet_forms']+=1
   v={n:1 for n in full['free']};lift=api['restore_assignment'](p,v,root=root);need(api['project_assignment'](p,lift,root=root)==v,'public inverse on graph');counts['public_graph_roundtrips']+=1
  records.append({'eliminated':list(selected),'operations':full['operations'],'degree':degree['exact_degree'],'witnesses':len(p['witnesses']),'equations':len(p['comparisons']),'leading_polynomial_sha256':sha(canonical(degree['full_leading_polynomial']).encode())})
 # Complete saved-record census, and own dominance calculation with duplicates.
 expected=[{k:v for k,v in q.items() if k!='leading_polynomial_sha256'} for q in records]
 need(same(expected,r['finite_family']['records']),'all family metadata')
 frontier=[q for q in expected if not any(v['operations']<=q['operations'] and v['degree']<=q['degree'] and(v['operations'],v['degree'])!=(q['operations'],q['degree']) for v in expected)]
 frontier.sort(key=lambda a:(-a['operations'],a['eliminated']));claimed=sorted(r['finite_family']['frontier'],key=lambda a:(-a['operations'],a['eliminated']));need(frontier==claimed,'family frontier')
 known=json.loads((root/'complete86_first_root_partitions.json').read_text())['census']['combined_frontier']
 oldpoints=[{'operations':q['operations'],'degree':q['exact_degree'],'witnesses':19,'origin':'frozen_first_root_grouping_union'}for q in known]
 pool=oldpoints+[dict(q,origin='selective_gap_graph_family')for q in frontier]
 combined=[q for q in pool if not any(v['operations']<=q['operations']and v['degree']<=q['degree']and(v['operations'],v['degree'])!=(q['operations'],q['degree'])for v in pool)]
 need(same(oldpoints,r['finite_family']['known_parent_frontier'])and same(combined,r['finite_family']['combined_operation_degree_frontier']),'independent combined frontier')
 p=packets[DEFAULT]
 def reject(f):
  try:f()
  except ValueError:counts['malformed_rejections']+=1
  else:raise AssertionError('malformed accepted')
 for key in p:
  q=copy.deepcopy(p);q.pop(key);reject(lambda q=q:api['checked'](q,root=root))
 for j in range(len(p['polynomial_source'])):
  q=copy.deepcopy(p);q['polynomial_source'][j][1]='+' if q['polynomial_source'][j][1]!='+' else '*';reject(lambda q=q:api['checked'](q,root=root))
 for selection in ([],list(DEFAULT),('q','q'),('C','q'),('bad',),(True,),None):reject(lambda selection=selection:api['build'](selection,root=root))
 for field in ('source','polynomial_source','witnesses','eliminated'):
  q=copy.deepcopy(p);q[field]=tuple(q[field]);reject(lambda q=q:api['checked'](q,root=root))
 for field in ('operations','M','A'):
  q=copy.deepcopy(p);q['polynomial_ledger'][field]=float(q['polynomial_ledger'][field]);reject(lambda q=q:api['degree_certificate'](q,root=root))
 q=copy.deepcopy(p);q['polynomial_source'][0][3]=True;reject(lambda:api['polynomial_source'](q,root=root))
 q=copy.deepcopy(parent);q['comparisons'][0].reverse();reject(lambda:api['rewrite'](q,root=root))
 v={n:1 for n in p['polynomial_ledger']['free']}
 for bad in (True,1.0,Fraction(1),None):
  z=dict(v);z['x']=bad;reject(lambda z=z:api['evaluate'](p,z,root=root))
 for flag in (0,1,None,'True'):reject(lambda flag=flag:api['evaluate'](p,v,signed=flag,root=root))
 for bad in (0,-1):
  z=dict(v);z['tau_gap']=bad;reject(lambda z=z:api['restore_assignment'](p,z,root=root))
 for extra in (False,True):
  z=dict(v)
  if extra:z['unused']=1
  else:z.pop('x')
  reject(lambda z=z:api['evaluate'](p,z,root=root))
 badgraph=api['restore_assignment'](p,v,root=root);badgraph['C']+=1;reject(lambda:api['project_assignment'](p,badgraph,signed=True,root=root))
 for name in ('source','polynomial_source','comparisons','witnesses'):
  q=api['build'](root=root);q[name].clear();need(same(api['build'](root=root),p),'private-copy boundary');counts['copy_isolation']+=1
 # Off-zero inverse must not be advertised as positive: make old tau too small.
 old=api['restore_assignment'](p,v,root=root);old['tau']=1;need(source_values(parent['source'],old)['first_root_base']>=1,'boundary fixture L')
 reject(lambda:api['project_assignment'](p,old,root=root));signed=api['project_assignment'](p,old,signed=True,root=root);need(signed['tau_gap']<=0,'signed graph inverse scope')
 with tempfile.TemporaryDirectory(prefix='review-gap113-') as tmp:
  dest=Path(tmp)
  for n in PARENT_PINS:(dest/n).write_bytes((root/n).read_bytes())
  api['build'](root=dest)
  for n in PARENT_PINS:
   raw=(dest/n).read_bytes();(dest/n).write_bytes(raw+b'\n');reject(lambda:api['build'](root=dest));(dest/n).write_bytes(raw);counts['warm_pin_rejections']+=1
 proc=subprocess.run([sys.executable,'-O',str(path),'--root',str(root)],capture_output=True,text=True,timeout=30);need(proc.returncode and 'without -O' in proc.stderr,'optimized-mode guard');counts['optimized_mode_rejections']+=1
 return {'status':'PASS_INDEPENDENT_SELECTIVE113','review_source_sha256':sha(Path(__file__).read_bytes()),'subject_pins':SUBJECT_PINS,'parent_pins':PARENT_PINS,'counts':dict(counts),'symbolic_identities':symbolic,'default_degree':default_degree,'family_frontier':frontier,'combined_frontier':combined,'records':records,'scope':'All256 literal sources, complete graph/SOS identity, full uniform leading forms and charged ledgers; bounded public API/copy/source-pin checks. No full universal positive Pell zero materialized.'}

def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--subject-root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root,v.subject_root)
 if v.expect:need(same(r,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
