"""Independent complete-source/API audit of the finite 37-partition compiler.

Explicit paths; pins checked before source-only execution. No author verify call.
Uses the frozen independent math review's sparse polynomial implementation and
partition enumerator, not the author's arithmetic/degree/census functions.
"""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
AUTHOR={'py':'ff9c9f43372aeac2b808f9ee8821011ea0e6ceff397225c934493ac26926da41','json':'d62818ee997fb0324da5d6d4105e28091b22dca25ae9f87871d87ae476f6e0a1','md':'d45817fbd03d2c5709bf39f90dd645428847308826eadfa011db050d53a2053a'}
MATH={'py':'165dc8479997282bcddff1edc728259831a07fbc89bda6d11c87ea646e1a8ed0','json':'b14112b3df1990c353f9006ab771dd5140da9fc1b6d8f01b6b53268a6254b547','md':'95047482d789166f49a9eca90a75d954459c90b1e35a54d4d82882e17724fb1a'}
OLD={'complete109_index_unit_tradeoffs107.py':'d255896294684f8d6411d992f5f0ba60a7f4051aa841d7e325f5347d64c23600','complete109_index_unit_tradeoffs107.json':'3d8d8d473cc866ebd585ac5605648839cfe014e98b5be2a10938cc0dfcfe12b3','complete109_index_unit_tradeoffs107.md':'928f760d73a7da081eace63cfcb144f41cd4271fcd92fbc3860d482738b16b9b'}
PORTS=('first_unit','main_unit','input_unit','aux_unit','index_unit');INDICES=(3,7,12,9,5)
DEGREES=(12,4,7,10,7);NAMES=['first','main','input','auxiliary','index']
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return list(sorted(a))==list(sorted(b))and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def load(path,pin,name):
 data=Path(path).read_bytes();need(sha(data)==pin,'source pin '+str(path));m=types.ModuleType(name);m.__file__=str(Path(path).resolve());exec(compile(data,m.__file__,'exec'),m.__dict__);return m

def pinned(path,pin):
 data=Path(path).read_bytes();need(sha(data)==pin,'artifact pin '+str(path));return data

def canonical_hash(v):return sha(json.dumps(v,sort_keys=True,separators=(',',':')).encode())
def run(rows,values):
 out=dict(values)
 for n,op,a,b in rows:
  x=a if type(a)is int else out[a];y=b if type(b)is int else out[b]
  out[n]=x+y if op=='+'else x-y if op=='-'else x*y
 return out

def schedule(core,kept,part):
 rows=copy.deepcopy(core);pairs=copy.deepcopy(kept);meta=[]
 for gi,block in enumerate(part):
  port=PORTS[block[0]]
  for j,k in enumerate(block[1:]):
   dst=f'unit_product_{gi}_{j}';rows.append([dst,'*',port,PORTS[k]]);port=dst
  meta.append(dict(parent_indices=[INDICES[i]for i in block],unit_ports=[PORTS[i]for i in block],product_port=port,comparison_index=len(pairs)))
  pairs.append([port,1])
 poly=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):poly += [[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']]
 out='square_0'
 for i in range(1,len(pairs)):
  dst=f'sum_{i}';poly.append([dst,'+',out,f'square_{i}']);out=dst
 return rows,pairs,poly,out,meta

def inspect(rows,free,fixed,roots):
 ready=set(free);deg={n:int(n not in fixed)for n in free};deps={};counts=Counter()
 for row in rows:
  need(type(row)is list and len(row)==4,'gate shape');n,op,a,b=row
  need(type(n)is str and n not in ready and op in('+','-','*'),'fresh gate')
  need(all(type(v)is int or type(v)is str and v in ready for v in(a,b)),'closed operands')
  d=[0 if type(v)is int else deg[v]for v in(a,b)];deg[n]=sum(d)if op=='*'else max(d);ready.add(n);deps[n]=(a,b);counts[op]+=1
 live={v for v in roots if type(v)is str}
 for n,op,a,b in reversed(rows):
  need(n in live,'dead gate '+n);live.update(v for v in(a,b)if type(v)is str)
 need(set(free)<=live,'unused coordinate')
 return dict(operations=len(rows),M=counts['*'],A=counts['+']+counts['-'],all_gates_live=True,free=sorted(free),literal_degree_upper_bound=max(0 if type(v)is int else deg[v]for v in roots))

def vectors(poly,variables):
 return sorted([[ [mon.count(n)for n in variables],co]for mon,co in poly.items()])

def verify(source,receipt,note,root,math_root):
 root=Path(root);math_root=Path(math_root)
 authorbytes={k:pinned(p,AUTHOR[k])for k,p in [('py',source),('json',receipt),('md',note)]}
 mb={k:pinned(math_root/('review_index_unit_partitions_math.'+k),pin)for k,pin in MATH.items()}
 math=load(math_root/'review_index_unit_partitions_math.py',MATH['py'],'independent_math');P=math.P
 saved=json.loads(authorbytes['json']);oldbytes={n:pinned(root/n,pin)for n,pin in OLD.items()};prior=json.loads(oldbytes['complete109_index_unit_tradeoffs107.json'])
 pins=dict(prior['parent_pins'],**OLD);need(exact(pins,saved['parent_pins']),'entire inherited dependency set');blobs={n:pinned(root/n,pin)for n,pin in pins.items()}
 for n,pin in math.PINS.items():pinned(root/n,pin)
 A=load(source,AUTHOR['py'],'reviewed_author');need(exact(A.PINS,pins),'actual module pins')
 need(saved['source_sha256']==AUTHOR['py'],'saved source identity');old=prior['canonical_parent'];need(exact(old,saved['canonical_parent'])and exact(old,A.canonical_parent(root=root)),'same canonical parent')
 core=prior['forms'][0]['packet']['source'][:75];kept=prior['forms'][0]['packet']['comparisons'][:8]
 need(all(x['packet']['source'][:75]==core for x in prior['forms']),'old common unit core');free=old['polynomial_ledger']['free'];fixed=old['fixed_numerals']
 env=math.execute(core,{n:P(n)for n in free});oe=math.execute(old['source'],{n:P(n)for n in free});get=lambda e,v:P(v)if type(v)is int else e[v]
 residuals=[get(oe,a)-get(oe,b)for a,b in old['comparisons']]
 for j,index in enumerate(INDICES):need(residuals[index]==(-1 if j==0 else 1)*(env[PORTS[j]]-1),'old unit residual sign')
 retained=[r for j,r in enumerate(residuals)if j not in INDICES];need(retained==[get(env,a)-get(env,b)for a,b in kept],'eight unchanged rows')
 degree=lambda p:max((sum(n not in fixed for n in mon)for mon in p),default=-1)
 top=lambda p:P({m:c for m,c in p.items()if sum(n not in fixed for n in m)==degree(p)})
 common=set(env)&set(oe);need(all(env[n]==oe[n]for n in common),'all common literal source polynomials');common_gates=len(common-set(free))
 leaders=[top(env[n])for n in PORTS];need([degree(env[n])for n in PORTS]==list(DEGREES),'literal unit exact degrees')
 math_saved=json.loads(mb['json']);need([[[list(m),v]for m,v in sorted(p.items())]for p in leaders]==math_saved['unit_highest_forms'],'same independently proved exact leaders')
 parts=[list(map(list,p))for p in math.partitions(5)];admitted=[p for p in parts if all(not(0 in b and 4 in b)for b in p)];excluded=[p for p in parts if p not in admitted]
 need(len(parts)==52 and len(admitted)==37 and len(excluded)==15,'independent canonical census')
 need(exact(parts,saved['all_set_partitions'])and exact(admitted,saved['admissible_partitions'])and exact(excluded,saved['excluded_criterion_only']),'saved entire census')
 need([f['packet']['partition']for f in saved['forms']]==admitted,'all saved forms once in census order')
 hist={str(g):sum(len(p)==g for p in admitted)for g in range(2,6)};need(exact(hist,saved['admissible_group_histogram']),'group histogram')
 counts=Counter(common_computed_coefficient_identities=common_gates,unit_residual_coefficient_identities=5,retained_residual_coefficient_identities=8);records=[];rng=random.Random(1092837)
 unitvars=[P(n)for n in NAMES];oldunit=sum(((u-1)**2 for u in unitvars),P())
 for part,f in zip(admitted,saved['forms']):
  c=f['packet'];built=A.build(part,root=root);need(exact(c,built),'public full build equals saved packet');need(exact(A.checked(c,root=root),c),'canonical check');need(exact(A.rewrite(old,part,root=root),c),'canonical rewrite')
  rows,pairs,poly,out,meta=schedule(core,kept,part)
  for key,value in [('source',rows),('comparisons',pairs),('polynomial_source',poly),('output',out),('unit_groups',meta)]:need(exact(c[key],value),'literal entire '+key)
  led=inspect(poly,free,fixed,[out]);cert=inspect(rows,free,fixed,[x for pair in pairs for x in pair]);need(exact(led,c['polynomial_ledger'])and exact(cert,c['certificate_ledger']),'independent complete ledgers')
  g=len(part);need((led['operations'],led['M'],led['A'],len(pairs),len(c['witnesses']))==(103+2*g,53,50+2*g,8+g,24),'full paid count formula')
  for field in('parameters','fixed_numerals','witnesses','domains'):need(exact(c[field],old[field]),'same supplied interface '+field)
  need(c['same_supplied_coordinates']is True,'same coordinates');need(exact(c['active_interfaces'],dict(old['active_interfaces'],index='index_unit')),'current active interfaces')
  defined=set(free)|{r[0]for r in rows}
  for v in c['active_interfaces'].values():need(all(n in defined for n in(v if type(v)is list else[v])),'live current interface')
  mapping=[]
  for j in range(13):
   if j not in INDICES:mapping.append(dict(parent_index=j,new_index=sum(i not in INDICES for i in range(j)),role='same_residual'))
   else:
    gi=next(i for i,m in enumerate(meta)if j in m['parent_indices']);mapping.append(dict(parent_index=j,new_index=8+gi,role='unit_group_member',old_residual_sign=-1 if j==3 else 1))
  need(exact(mapping,c['parent_comparison_map']),'all parent comparison metadata')
  rawmap=copy.deepcopy(old['original_raw_comparison_map'])
  for m in rawmap:
   if m['new_index']is None:m['role']='historical_positive_definition'
   else:cur=mapping[m['new_index']];m['new_index']=cur['new_index'];m['role']=cur['role']
  need(exact(rawmap,c['original_raw_comparison_map']),'all original raw comparison metadata')
  need(exact(c['unit_interfaces'],dict(zip(NAMES,PORTS))),'all current unit interfaces')
  sp=f['source_proof'];need(sp['common_computed_gate_identities']==common_gates and sp['unchanged_supplied_leaves']==len(free)and sp['unchanged_residuals']==8 and exact(sp['literal_unit_groups'],meta),'saved literal source-proof claims')
  need(exact(sp['index_residual_identity'],[[[0,0,0],-1],[[0,0,1],-1],[[0,1,0],-1],[[1,0,0],1]]),'saved index affine identity')
  hist_expected={'parent_variant':old['variant'],'parent_exact_degree':old['exact_polynomial_degree'],'parent_ledger':old['polynomial_ledger'],'parent_scale':old['scale'],'parent_coordinate_relation':old['coordinate_relation'],'parent_historical_definitions':old['historical_parent'],'parent_original_raw_comparison_map':old['original_raw_comparison_map']}
  need(exact(hist_expected,c['historical_provenance']),'historical provenance remains historical')
  group_leads=[];group_units=[]
  for block in part:
   lp=P(1);up=P(1)
   for j in block:lp*=leaders[j];up*=unitvars[j]
   group_leads.append(lp);group_units.append(up)
  ds=[degree(r)for r in retained]+[degree(p)for p in group_leads];D=max(ds);maxima=[i for i,d in enumerate(ds)if d==D];tops=[top(r)for r in retained]+group_leads
  lead=sum((tops[i]**2 for i in maxima),P());need(degree(lead)==2*D,'nonzero summed maximal squares')
  dc=f['degree_certificate'];need(exact(dc,A.degree_certificate(c,root=root)),'public canonical degree certificate')
  expected={'exact_degree':2*D,'unit_order':NAMES,'unit_degrees':list(DEGREES),'residual_exact_degrees':ds,'maximal_residual_indices':maxima,'variables':free,'degree_weights':[int(n not in fixed)for n in free],'highest_homogeneous_polynomial':vectors(lead,free),'fixed_parameter_dependencies':sorted({n for mon in lead for n in mon if n in fixed}),'literal_propagated_upper':led['literal_degree_upper_bound']}
  for k,v in expected.items():need(exact(dc[k],v),'exact full degree field '+k)
  sample=Counter()
  for mon,v in lead.items():sample[mon.count('Bm1')]+=v*2**mon.count('tau_gap')
  sample={k:v for k,v in sample.items()if v};need(all(v>0 for v in sample.values()),'fixed-slice nonzero witness');need(dc['positive_Bm1_witness']==[[k,v]for k,v in sorted(sample.items())],'univariate degree witness')
  special=None
  if part==[[0],[1,3],[2,4]]:
   powers={'ga':4,'a':4,'i':4,'j':4,'c':12};mon=tuple(sorted(n for n,e in powers.items()for _ in range(e)));need(lead[mon]==256,'default exact coefficient256');special=dict(powers=powers,coefficient=256)
  need(exact(dc['special_default_coefficient'],special)and c['exact_polynomial_degree']==2*D,'current exact degree')
  correction=sum(((u-1)**2 for u in group_units),P())-oldunit
  need(exact(f['complete_correction']['coefficients'],vectors(correction,NAMES))and f['complete_correction']['unit_order']==NAMES,'complete symbolic five-unit correction')
  need(c['full_polynomial_identity']is(not correction)and(not correction)==(g==5),'singleton identity exception')
  for case in range(4):
   values={n:rng.randint(-3,4)if case<2 else rng.randint(1,5)for n in free};values.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   if case==1:values={n:v if n in fixed else Fraction(v,7)for n,v in values.items()}
   before=run(old['polynomial_source'],values);after=run(poly,values);uv={n:after[p]for n,p in zip(NAMES,PORTS)};delta=0
   for mon,coef in correction.items():
    for n in mon:coef*=uv[n]
    delta+=coef
   need(after[out]-before[old['output']]==delta,'entire polynomial numerical correction')
   for i,r in enumerate(mapping):
    x,y=old['comparisons'][i];lhs=(x if type(x)is int else before[x])-(y if type(y)is int else before[y])
    if r['role']=='same_residual':x,y=pairs[r['new_index']];rhs=(x if type(x)is int else after[x])-(y if type(y)is int else after[y])
    else:rhs=r['old_residual_sign']*(after[PORTS[INDICES.index(i)]]-1)
    need(lhs==rhs,'literal numerical parent residual');counts['parent_residual_values']+=1
   if case!=1:need(A.evaluate(c,values,signed=case==0,root=root)==after[out],'public evaluation');counts['public_evaluations']+=1
   counts['full_corrections']+=1;counts['signed_cases']+=case<2;counts['rational_cases']+=case==1
  records.append(dict(partition=part,source_sha256=canonical_hash(poly),source_proof_sha256=canonical_hash(f['source_proof']),complete_correction_sha256=canonical_hash(f['complete_correction']),degree_certificate_sha256=canonical_hash(dc),operations=led['operations'],M=led['M'],A=led['A'],degree=2*D,maximal_residual_indices=maxima,highest_terms=len(lead)))
  counts.update(forms=1,complete_gates=len(poly),M=led['M'],A=led['A'],certificate_gates=len(rows),comparisons=len(pairs),exact_degree_certificates=1,symbolic_corrections=1,metadata_packets=1)
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guard_rejections']+=1
  else:raise ValueError('Malformed public call accepted')
 for part in excluded:reject(lambda part=part:A.build(part,root=root))
 for part in(True,1,1.0,'all',(),[],[[0,1,2,3]],[[0],[1],[2],[3],[4],[4]],[[0],[True],[2],[3],[4]],[[0],[1.0],[2],[3],[4]],[[1],[0],[2],[3],[4]],[[0],[3,1],[2,4]],[[0],[],[1],[2],[3],[4]],[(0,),[1],[2],[3],[4]]):reject(lambda part=part:A.build(part,root=root))
 c=A.build(root=root);need(c['partition']==[[0],[1,3],[2,4]],'default');one={n:1 for n in free}
 for field in c:
  q=copy.deepcopy(c);q.pop(field);reject(lambda q=q:A.checked(q,root=root))
 for path in [('source',),('comparisons',),('polynomial_source',),('partition',),('unit_groups',),('parent_comparison_map',),('witnesses',)]:
  q=copy.deepcopy(c);q[path[0]]=tuple(q[path[0]]);reject(lambda q=q:A.checked(q,root=root))
 for field in ('operations','M','A'):
  q=copy.deepcopy(c);q['polynomial_ledger'][field]=float(q['polynomial_ledger'][field]);reject(lambda q=q:A.checked(q,root=root))
 for f,v in [('exact_polynomial_degree',28.0),('full_polynomial_identity',0),('same_supplied_coordinates',1),('output','first_unit')]:
  q=copy.deepcopy(c);q[f]=v
  for api in(A.checked,A.degree_certificate,A.polynomial_source):reject(lambda api=api,q=q:api(q,root=root))
 q=copy.deepcopy(c);q['polynomial_source'][-1][1]='-';reject(lambda:A.checked(q,root=root))
 for field in('source','comparisons','witnesses','domains'):
  q=copy.deepcopy(old);q[field]=None;reject(lambda q=q:A.rewrite(q,root=root))
 for n,v in [('x',0),('x',-1),('a',True),('a',1.0),('r',Fraction(1,1)),('Bm1',0)]:
  values=dict(one);values[n]=v;reject(lambda values=values:A.evaluate(c,values,root=root))
 for values in ({},dict(one,extra=1),{k:v for k,v in one.items()if k!='x'},list(one)):
  reject(lambda values=values:A.evaluate(c,values,root=root))
 for signed in (1,0,None,'true'):reject(lambda signed=signed:A.evaluate(c,one,signed=signed,root=root))
 for n,v in [('x',True),('x',1.0),('a',Fraction(2,1))]:
  values=dict(one);values[n]=v;reject(lambda values=values:A.evaluate(c,values,signed=True,root=root))
 for field in('source','polynomial_source','partition','unit_groups','parent_comparison_map','historical_provenance','witnesses','active_interfaces'):
  q=A.build(root=root);q[field].clear();need(exact(A.build(root=root),c),'build defensive isolation');counts['copy_checks']+=1
 for api in(A.canonical_parent,):
  q=api(root=root);q['source'].clear();need(exact(api(root=root),old),'parent defensive isolation');counts['copy_checks']+=1
 q=A.polynomial_source(c,root=root);q.clear();need(exact(A.checked(c,root=root),c),'source accessor isolation');counts['copy_checks']+=1
 q=A.degree_certificate(c,root=root);q['highest_homogeneous_polynomial'].clear();need(A.degree_certificate(c,root=root)['highest_homogeneous_polynomial'],'degree defensive isolation');counts['copy_checks']+=1
 part=[[0],[1,3],[2,4]];q=A.build(part,root=root);part[0].append(1);need(exact(q,c),'input partition copied');counts['copy_checks']+=1
 with tempfile.TemporaryDirectory(prefix='review_unit_partitions_')as tmp:
  private=Path(tmp)/'papers'/'research-wip'/'native-stream-queue';private.mkdir(parents=True)
  for name,data in blobs.items():
   path=private/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
   if '/'in name:(private/Path(name).name).write_bytes(data)
  A.build(root=private)
  for name,data in blobs.items():
   path=private/name;path.write_bytes(data+b'\n');reject(lambda:A.build(root=private));path.write_bytes(data);counts['warm_pin_rejections']+=1
  counts['relative_pins_rejected_despite_valid_flat_fallback']=sum('/'in n for n in blobs)
 proc=subprocess.run([sys.executable,'-O',str(Path(source).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and 'run without -O'in proc.stderr,'optimized execution guard');counts['optimized_rejections']=1
 points={(r['operations'],r['degree'])for r in records};frontier=sorted(p for p in points if not any(q!=p and q[0]<=p[0]and q[1]<=p[1]for q in points));need([list(p)for p in frontier]==saved['family_frontier'],'finite frontier')
 winners=[dict(operations=o,degree=d,partitions=[r['partition']for r in records if(r['operations'],r['degree'])==(o,d)])for o,d in frontier];need(exact(winners,saved['frontier_schedules']),'winner multiplicities')
 need(counts['complete_gates']==4039 and counts['M']==1961 and counts['A']==2078,'full paid aggregate')
 return dict(status='PASS_INDEPENDENT_COMPLETE_UNIT_PARTITION_FRONTIER109',author_pins=AUTHOR,independent_math_pins=MATH,dependency_pins=pins,counts=dict(counts),census=dict(total=52,admitted=37,excluded_criterion_only=15,group_histogram=hist),forms=records,frontier=winners,scope='Independent reconstruction of all37 literal complete sources, five exact unit residual cuts, eight unchanged rows, all degree/correction polynomials and current/historical metadata; strict public API, copies and warm pins. Uses frozen independent math sparse-polynomial class/enumerator. General integer zero theorem is a proof, not inferred from finite evaluations. No original universal zero materialized, no claim excluded15 are unsound, no unrestricted arithmetic optimum or new source-input theorem.')

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for name in('source','receipt','note','root','math-root','output'):ap.add_argument('--'+name,required=True,type=Path)
 ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.source,a.receipt,a.note,a.root,a.math_root)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact typed saved receipt mismatch')
 a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':out['status'],'counts':out['counts'],'frontier':out['frontier']},sort_keys=True))
if __name__=='__main__':main()
