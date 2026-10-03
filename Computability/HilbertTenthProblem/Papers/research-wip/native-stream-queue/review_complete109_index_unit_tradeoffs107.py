#!/usr/bin/env python3
"""Independent complete index-unit grouping audit."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
SUBJECT_PINS={'complete109_index_unit_tradeoffs107.py': 'd255896294684f8d6411d992f5f0ba60a7f4051aa841d7e325f5347d64c23600', 'complete109_index_unit_tradeoffs107.json': '3d8d8d473cc866ebd585ac5605648839cfe014e98b5be2a10938cc0dfcfe12b3', 'complete109_index_unit_tradeoffs107.md': '928f760d73a7da081eace63cfcb144f41cd4271fcd92fbc3860d482738b16b9b'}
PARENT_PINS={'complete74_gap_selective_projection113.py': '573f1e8b0c89ef039a2a7fc40bad959cf7e362bcec4c96b3536974e7b71316c4', 'complete74_gap_selective_projection113.json': '2636f00a9e67f53a144986382442f456427257d498e33960e023e9c986b6b9c3', 'complete74_gap_selective_projection113.md': '3539d2fa0721eb8448409d075261a6508cc7adc1d887e3905cfeaed737396afa', 'complete74_factored_first_norm.py': '7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete74_factored_first_norm.md': '119b51ca9a5d50e0eb998b334af87c1ea3eb0913f956b4f9d7a985f5d1159d9f', 'complete75_positive_elimination.py': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749', 'complete75_positive_elimination.json': '03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703', 'complete75_positive_elimination.md': '59cc280280bb8ab74318f648da56aabf31317f42a8a08d01851c5f8db0232d6b', 'complete75_positive_root89.py': 'f850ee8cd5e00b9235a8f192d2f95f6b27cf72a40c3f6b6e3fa054700d793c72', 'complete75_positive_root89.md': '7b85195a800b909e3bf6e55fa85decfaa08299cf1e100efa866659571d192085', 'complete86_first_root_partitions.json': '7535a1b2d36f802d6d72bab5c7cfe807c90b802398ed817ea990b76240b7cdc5', 'complete113_main_input_units111.py': '152905dd07e507289fe9f321982f5e680ec34b6a3ef23f7205bd370ad6623d16', 'complete113_main_input_units111.json': 'b9702ea066114aec3aef374a480fb2049f47a47d1daf580ea42e595107ebee87', 'complete113_main_input_units111.md': '9f73c0d51f5e1fe9237b0ffc3cbbba49f93b08a0b6242693425f0e086897905f', '../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d', '../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90', '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992', 'complete113_asymmetric_retained109.py': '5017530a67107651cbde1cbfd81e4a2cf0aad294bb81997789e8e749a1ea2368', 'complete113_asymmetric_retained109.json': '8a037d2830ef3cbbfe7f0b02b71b5337ffac8a3e34cf8391c09257d0babb9f24', 'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0'}
MODES=('degree32','degree42')
GROUPS={'degree32':(('first','main'),('index','input'),('aux',)), 'degree42':(('first','input'),('index','main','aux'))}
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

def structural(parent,p,mode):
 free=parent['polynomial_ledger']['free'];rows=parent['source'];by={n:[o,a,b]for n,o,a,b in rows}
 need(by['r1']==['+','r',1]and by['R11']==['+','r1','hpm1'],'actual old index sides')
 need([r[0]for r in rows if 'r1'in r[2:]]==['R11'],'private r+1 source consumers')
 need(not any('R11'in r[2:]for r in rows),'private final index side')
 need(parent['comparisons'].count(['R10b','R11'])==1 and sum('r1'in c or'R11'in c for c in parent['comparisons'])==1,'exact old index comparison consumer')
 need(by['R10b']==['+','eta','zeta']and by['hpm1']==['*','h','UM'],'actual computed k and paid hE')
 d=DAG();old=d.run(rows,free);new=d.run(p['source'],free);get=lambda env,v:d.a(v)if type(v)is int else env[v]
 units={'first':d.op('+',old['tau_square'],old['L9']),'main':d.op('-',old['L15'],old['Ac2']),'input':d.op('-',old['mu2'],old['scaled_kappa2']),'aux':d.op('+',old['L17'],old['aux_y2']),'index':d.op('-',d.op('-',old['R10b'],old['r']),old['hpm1'])}
 positions={'first':3,'main':7,'input':12,'aux':9,'index':5}
 expected=[(get(old,a),get(old,b))for j,(a,b)in enumerate(parent['comparisons'])if j not in positions.values()]
 explained={old[n]for n,_,_,_ in rows}|set(units.values())|{d.op('-',old['R10b'],old['r'])}
 for group in GROUPS[mode]:
  expr=units[group[0]]
  for name in group[1:]:expr=d.op('*',expr,units[name]);explained.add(expr)
  expected.append((expr,d.a(1)))
 actual=[(get(new,a),get(new,b))for a,b in p['comparisons']]
 need(Counter(actual)==Counter(expected),'all unchanged and grouped complete comparison expressions')
 common=set(old)&set(new);need(all(old[n]==new[n]for n in common),'all retained registers and leaves')
 need(all(new[n]in explained for n,_,_,_ in p['source']),'every new operation explained')
 need('r1'not in new and 'R11'not in new,'old private index pair deleted')
 for key in('parameters','fixed_numerals','witnesses','domains'):need(exact(p[key],parent[key]),'complete unchanged interface '+key)
 poly,out=finalizer(p['source'],p['comparisons']);need(poly==p['polynomial_source']and out==p['output'],'whole literal SOS finalizer')
 cert=ledger(p['source'],free,[v for pair in p['comparisons']for v in pair]);whole=ledger(poly,free,[out])
 for key in cert:
  if key in p['certificate_ledger']:need(exact(cert[key],p['certificate_ledger'][key]),'certificate ledger '+key)
 for key in whole:
  if key in p['polynomial_ledger']:need(exact(whole[key],p['polynomial_ledger'][key]),'whole polynomial ledger '+key)
 want=(77,42,35,11,109,53,56)if mode=='degree32'else(78,43,35,10,107,53,54)
 need((cert['operations'],cert['M'],cert['A'],len(actual),whole['operations'],whole['M'],whole['A'])==want,'fully paid actual counts')
 return {'common_registers_and_leaves':len(common),'retained_ungrouped_comparisons':8,'complete_comparison_expressions':len(actual),'certificate':cert,'polynomial':whole}

def leading(parent,mode):
 e={v:(0 if v in CONST else 1,atom(v))for v in parent['polynomial_ledger']['free']}
 def A(x,y,sign=1):
  d=max(x[0],y[0]);return d,add(x[1]if x[0]==d else{},y[1]if y[0]==d else{},sign)
 def M(x,y):return x[0]+y[0],mul(x[1],y[1])
 def G(v):return(0,atom(v))if type(v)is int else e[v]
 for n,o,a,b in parent['source']:e[n]=M(G(a),G(b))if o=='*'else A(G(a),G(b),1 if o=='+'else-1)
 def norm(z,v):return A(A(M((0,atom(2)),M(M(G('a'),z),v)),M(v,v)),M(G('a4m5'),M(z,z)),-1)
 units={'first':A(G('tau_square'),G('L9')),'main':norm(G('c'),A(G('wn2'),G('gam'))),'input':norm(G('index_rhs'),A(G('W'),G('modulus_multiple'))),'aux':A(G('L17'),G('aux_y2')),'index':A(A(G('R10b'),G('r'),-1),G('hpm1'),-1)}
 positions=(3,7,12,9,5);res=[A(G(a),G(b),-1)for i,(a,b)in enumerate(parent['comparisons'])if i not in positions]
 for group in GROUPS[mode]:
  v=units[group[0]]
  for name in group[1:]:v=M(v,units[name])
  res.append(A(v,(0,atom(1)),-1))
 D=max(d for d,p in res);top={}
 for d,p in res:
  if d==D:top=add(top,mul(p,p))
 b,J,w,s,g,a,c,delta,i,j,h=map(atom,('Bm1','Jrep','w','s','tau_gap','a','c','delta','i','j','h'));k=add(atom('eta'),atom('zeta'))
 L=mul(mul(mul(power(b,7),power(J,7)),mul(w,power(s,2))),k);first=mul(L,add(add(g,g),k,-1))
 v=add(mul(mul(b,w),J),mul(atom(4),mul(a,atom('ga'))));main=mul(v,add(mul(atom(2),mul(a,c)),v))
 index=mul(atom(-1),mul(mul(power(b,4),power(J,4)),mul(mul(h,w),s)))
 aux=mul(power(i,2),mul(power(j,2),power(c,6)))
 expected=power(mul(first,main),2)if mode=='degree32'else power(mul(mul(index,main),aux),2)
 need(top==expected,'entire uniform leading homogeneous polynomial')
 need(2*D==(32 if mode=='degree32'else 42),'exact full degree')
 return {'exact_degree':2*D,'residual_upper_degrees':[d for d,p in res],'unit_degrees':{k:d for k,(d,p)in units.items()},'full_leading_homogeneous_polynomial':[[list(m),v]for m,v in sorted(top.items())]}

def identities():
 k,r,H=map(atom,('k','r','hE'));one=atom(1)
 old=add(k,add(add(r,one),H),-1);unit=add(add(k,r,-1),H,-1);need(old==add(unit,one,-1),'all-value index residual equality')
 norms={n:atom(n)for n in('first','main','input','aux','index')};base={}
 for p in norms.values():v=add(p,one,-1);base=add(base,mul(v,v))
 corrections={}
 for mode in MODES:
  new={}
  for group in GROUPS[mode]:
   p=one
   for name in group:p=mul(p,norms[name])
   v=add(p,one,-1);new=add(new,mul(v,v))
  corrections[mode]=[[list(m),c]for m,c in sorted(add(new,base,-1).items())]
 return {'index_residual':[[list(m),v]for m,v in sorted(old.items())],'complete_sos_corrections':corrections}

def verify(root,subject):
 for name,pin in SUBJECT_PINS.items():need(sha((subject/name).read_bytes())==pin,'frozen author pin '+name)
 for name,pin in PARENT_PINS.items():need(sha((root/name).read_bytes())==pin,'strict inherited pin '+name)
 author=json.loads((subject/'complete109_index_unit_tradeoffs107.json').read_text())
 inherited=json.loads((root/'complete113_asymmetric_retained109.json').read_text());parent=next(f['packet']for f in inherited['forms']if f['packet']['variant']=='sos')
 path=subject/'complete109_index_unit_tradeoffs107.py';api={'__name__':'_review_index107','__file__':str(path)};exec(compile(path.read_bytes(),str(path),'exec'),api)
 forms={f['packet']['variant']:f for f in author['forms']};need(len(author['forms'])==2 and set(forms)==set(MODES),'exact two new forms')
 need(exact(api['canonical_parent'](root=root),parent),'entire selected frozen asymmetric113 parent')
 algebra=identities();counts=Counter();reports=[];rng=random.Random(1074232)
 def reject(call):
  try:call()
  except ValueError:counts['malformed_rejections']+=1
  else:raise AssertionError('invalid call accepted')
 for mode in MODES:
  packet=forms[mode]['packet'];need(exact(packet,api['build'](mode,root=root)),'complete emitted canonical packet')
  proof=structural(parent,packet,mode);degree=leading(parent,mode);need(degree['exact_degree']==packet['exact_polynomial_degree'],'current exact degree')
  counts['complete_circuits']+=1;counts['complete_live_gates']+=len(packet['polynomial_source']);counts['source_gate_rows']+=len(packet['source']);counts['complete_comparisons']+=len(packet['comparisons']);counts['uniform_full_leading_forms']+=1
  reports.append({'variant':mode,'structural':proof,'degree':degree})
  names={'first':'first_unit','main':'main_unit','input':'input_unit','aux':'aux_unit','index':'index_unit'};positions={'first':3,'main':7,'input':12,'aux':9,'index':5}
  expectedgroups=[];mapping=[None]*13;plain=[i for i in range(13)if i not in positions.values()]
  for ni,oi in enumerate(plain):mapping[oi]={'parent_index':oi,'new_index':ni,'role':'same_residual'}
  for gi,group in enumerate(GROUPS[mode]):
   ni=len(plain)+gi;port=packet['comparisons'][ni][0]
   expectedgroups.append({'parent_indices':[positions[n]for n in group],'unit_ports':[names[n]for n in group],'product_port':port,'comparison_index':ni})
   for name in group:
    oi=positions[name];mapping[oi]={'parent_index':oi,'new_index':ni,'role':'unit_group_member','old_residual_sign':-1 if name=='first'else 1}
  need(exact(expectedgroups,packet['unit_groups'])and exact(mapping,packet['parent_comparison_map']),'complete current group/map metadata')
  raw=[]
  for item in parent['original_raw_comparison_map']:
   item=copy.deepcopy(item);oi=item['new_index']
   if oi is not None:item.update(new_index=mapping[oi]['new_index'],role=mapping[oi]['role'])
   else:item['role']='historical_positive_definition'
   raw.append(item)
  need(exact(raw,packet['original_raw_comparison_map']),'complete original raw map')
  need(exact(packet['active_interfaces'],dict(parent['active_interfaces'],index='index_unit'))and packet['same_supplied_coordinates']is True,'current ports and coordinate scope')
  # Compare saved leading-form and correction evidence with independently
  # derived sparse coefficient dictionaries, not just numeric degrees.
  cert=forms[mode]['degree_certificate'];variables=cert['variables'];saved={}
  for powers,c in cert['highest_homogeneous_polynomial']:
   mon=tuple(sorted(n for n,power in zip(variables,powers)for _ in range(power)));saved[mon]=c
  need(saved=={tuple(m):c for m,c in degree['full_leading_homogeneous_polynomial']},'saved full leading coefficient certificate')
  correction=forms[mode]['complete_correction'];saved={}
  for powers,c in correction['coefficients']:
   mon=tuple(sorted(('aux'if n=='auxiliary'else n)for n,power in zip(correction['unit_order'],powers)for _ in range(power)));saved[mon]=c
  need(saved=={tuple(m):c for m,c in algebra['complete_sos_corrections'][mode]},'saved full correction coefficients')
  for case in range(96):
   vals={n:rng.randint(-5,5)if case<48 else rng.randint(1,5)for n in packet['polynomial_ledger']['free']}
   if case>=72:vals={n:Fraction(v,3)for n,v in vals.items()};counts['rational_cases']+=1
   old=run(parent['polynomial_source'],vals);new=run(packet['polynomial_source'],vals)
   units={'first':old['tau_square']+old['L9'],'main':old['L15']-old['Ac2'],'input':old['mu2']-old['scaled_kappa2'],'aux':old['L17']+old['aux_y2'],'index':old['R10b']-vals['r']-old['hpm1']}
   need(units['index']-1==old['R10b']-old['R11'],'exact local index residual value')
   correction=sum(c*prod(units[n]for n in mon)for mon,c in algebra['complete_sos_corrections'][mode])
   need(new[packet['output']]-old[parent['output']]==correction,'entire exact SOS correction');counts['full_correction_values']+=1;counts['signed_cases']+=case<48
   for n in set(old)&set(new):
    if n.startswith(('residual_','square_','sum_')):continue
    need(old[n]==new[n],'all common pre-finalizer registers');counts['common_value_checks']+=1
   get=lambda env,v:v if type(v)is int else env[v]
   for i,pair in enumerate(parent['comparisons']):
    if i in(3,5,7,9,12):continue
    need(pair in packet['comparisons'],'unchanged comparison retained');a,b=pair;need(get(old,a)-get(old,b)==get(new,a)-get(new,b),'retained residual value');counts['retained_residual_values']+=1
   if case in(0,48):need(api['evaluate'](packet,vals,signed=case==0,root=root)==new[packet['output']],'public complete evaluator');counts['public_evaluations']+=1
  for field in packet:
   bad=copy.deepcopy(packet);del bad[field];reject(lambda bad=bad:api['checked'](bad,root=root))
  for i in range(len(packet['polynomial_source'])):
   bad=copy.deepcopy(packet);bad['polynomial_source'][i][1]='+'if bad['polynomial_source'][i][1]!='+'else'*';reject(lambda bad=bad:api['checked'](bad,root=root))
  for field in('source','comparisons','witnesses','fixed_numerals'):
   bad=copy.deepcopy(packet);bad[field]=tuple(bad[field]);reject(lambda bad=bad:api['checked'](bad,root=root))
  bad=copy.deepcopy(packet);bad['exact_polynomial_degree']=float(bad['exact_polynomial_degree']);reject(lambda:api['degree_certificate'](bad,root=root))
  bad=copy.deepcopy(parent);bad['source'][0][1]='*';reject(lambda:api['rewrite'](bad,mode,root=root))
  one={n:1 for n in packet['polynomial_ledger']['free']}
  for value in(True,1.0,Fraction(1),0,-1):
   bad=dict(one);bad['x']=value;reject(lambda bad=bad:api['evaluate'](packet,bad,root=root))
  reject(lambda:api['evaluate'](packet,one,signed=1,root=root))
  for field in('source','polynomial_source','comparisons','witnesses'):
   fresh=api['build'](mode,root=root);fresh[field].clear();need(exact(api['build'](mode,root=root),packet),'defensive returned copies');counts['copy_checks']+=1
 for a in range(4):
  for d in range(4):
   for c in range(4):need((d*d-(a*a+4*a+3)*c*c)%4!=3,'protected main/input norm');counts['main_input_residue_cases']+=1
 for t in range(4):
  for u in range(4):
   for y in range(4):need((t*t*(u*u-y*y)+y*y)%4!=3,'protected auxiliary norm');counts['auxiliary_residue_cases']+=1
 import itertools
 for mode in MODES:
  for group in GROUPS[mode]:need(sum(n in('first','index')for n in group)<=1,'at most one unprotected unit per group')
  for first,index,main,inp,aux in itertools.product(range(-3,4),range(-3,4),(-3,-2,0,1,2,3),(-3,-2,0,1,2,3),(-3,-2,0,1,2,3)):
   u={'first':first,'index':index,'main':main,'input':inp,'aux':aux}
   newzero=all(prod(u[n]for n in group)==1 for group in GROUPS[mode]);need(newzero==all(v==1 for v in u.values()),'bounded independent integer unit-pattern census');counts['unit_pattern_cases']+=1
 for value in(None,True,1,[],{},'bad'):reject(lambda value=value:api['build'](value,root=root))
 with tempfile.TemporaryDirectory(prefix='review-index107-')as tmp:
  dest=Path(tmp)/'Papers'/'research-wip'/'native-stream-queue';dest.mkdir(parents=True)
  for name in PARENT_PINS:
   q=dest/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((root/name).read_bytes())
  api['build'](root=dest)
  for name in PARENT_PINS:
   q=dest/name;data=q.read_bytes();q.write_bytes(data+b'\n')
   if '/'in name:(dest/Path(name).name).write_bytes(data)
   reject(lambda:api['build'](root=dest));q.write_bytes(data);counts['warm_pin_rejections']+=1
   if '/'in name:counts['relative_proof_rejections']+=1
 proc=subprocess.run([sys.executable,'-O',str(path),'--root',str(root)],capture_output=True,text=True,timeout=30);need(proc.returncode and 'without -O'in proc.stderr,'optimized execution rejected');counts['optimized_rejections']+=1
 previous=[tuple(p)for p in inherited['known_union_frontier']];points=[(p['packet']['polynomial_ledger']['operations'],p['packet']['exact_polynomial_degree'])for p in forms.values()]
 combined=sorted({p for p in previous+points if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in previous+points)})
 need(exact([list(p)for p in combined],author['known_union_frontier']),'independent measured frontier union')
 return {'status':'PASS_INDEPENDENT_INDEX_UNIT107','review_source_sha256':sha(Path(__file__).read_bytes()),'subject_pins':SUBJECT_PINS,'parent_pins':PARENT_PINS,'counts':dict(counts),'algebraic_identities':algebra,'forms':reports,'combined_frontier':[list(p)for p in combined],'scope':'Two literal full source/ledger/leading-form reconstructions, complete all-value SOS corrections and full integer-zero grouping proof. Same supplied positive interface inherits the frozen asymmetric universal theorem; no new scale map or full universal Pell witness is claimed.'}
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',type=Path,required=True);a.add_argument('--subject-root',type=Path,required=True);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);v=a.parse_args();r=verify(v.root,v.subject_root)
 if v.expect:need(exact(r,json.loads(v.expect.read_text())),'exact saved receipt')
 if v.output:v.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
