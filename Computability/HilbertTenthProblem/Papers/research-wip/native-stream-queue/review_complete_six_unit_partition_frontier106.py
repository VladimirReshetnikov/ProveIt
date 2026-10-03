#!/usr/bin/env python3
"""Independent maintained151-source review; prior scout authorship disclosed."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'complete_six_unit_partition_frontier106.py':'6e5f62fef301b5d78f02f98d1c71f70551631feb99f05b94a89e5b1e1dc8cec0',
'complete_six_unit_partition_frontier106.json':'eb2076b1285470a4e8ec8ee7d92b0dad83f947737d5dc0cd2580eb06e9770b3b',
'complete_six_unit_partition_frontier106.md':'e6dc5b0bbbe8077f56cfee604505cd9669ac63e2a58ee942dc53a14aa1256aaa',
'complete_bound_unit_scout.py':'61a4292aa1623999e1116cc5b803e01b1b7c240e99f35bc1408c1b7e73c1e0c6',
'complete_bound_unit_scout.json':'53c43e4792e4d89cf7ea54aa45a1511caff8e03b2ca9035bd230623c28a6cc78',
'complete_bound_unit_scout.md':'100d6b1b3869900cd2816a93f70211237458a943e2e50c70ba4cf2fd429d2acb'}

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def load(path,pin,name):
 data=path.read_bytes();need(sha(data)==pin,'module source pin');m=types.ModuleType(name);m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m
class Interner:
 def __init__(self):self.nodes={}
 def atom(self,k):
  if k not in self.nodes:self.nodes[k]=len(self.nodes)
  return self.nodes[k]
 def run(self,rows,free):
  d={v:self.atom(('var',v))for v in free}
  for n,o,a,b in rows:d[n]=self.atom((o,self.atom(('int',a))if type(a)is int else d[a],self.atom(('int',b))if type(b)is int else d[b]))
  return d

def verify(root,artifacts):
 for name,pin in PINS.items():need(sha((artifacts/name).read_bytes())==pin,'artifact pin '+name)
 author=load(artifacts/'complete_six_unit_partition_frontier106.py',PINS['complete_six_unit_partition_frontier106.py'],'_review_six_author')
 scout=load(artifacts/'complete_bound_unit_scout.py',PINS['complete_bound_unit_scout.py'],'_review_six_scout')
 saved=json.loads((artifacts/'complete_six_unit_partition_frontier106.json').read_text());prior=json.loads((artifacts/'complete_bound_unit_scout.json').read_text())
 # Authenticate actual dependency bytes independently of the author's reader.
 # The expected inventory comes from the separately pinned scout provenance,
 # the frozen37 trio, and the scout trio; no new author assertion supplies it.
 expected_pins=dict(prior['transitive_pins'],**prior['pins'])
 expected_pins.update({'complete_unit_partition_frontier109.py':'ff9c9f43372aeac2b808f9ee8821011ea0e6ceff397225c934493ac26926da41','complete_unit_partition_frontier109.json':'d62818ee997fb0324da5d6d4105e28091b22dca25ae9f87871d87ae476f6e0a1','complete_unit_partition_frontier109.md':'d45817fbd03d2c5709bf39f90dd645428847308826eadfa011db050d53a2053a'})
 expected_pins.update({n:h for n,h in PINS.items()if n.startswith('complete_bound_unit_scout.')})
 blobs={}
 for name,pin in expected_pins.items():
  paths=[root/name,root/Path(name).name,artifacts/name,artifacts/Path(name).name];path=next((q for q in paths if q.exists()),paths[0]);data=path.read_bytes()
  need(sha(data)==pin,'independent actual dependency pin '+name);blobs[name]=data
 need(exact(expected_pins,author.PINS)and exact(expected_pins,saved['parent_pins']),'entire independent dependency manifest')
 need(exact(blobs,author.authenticated(root)),'actual author input bytes match independent reader')
 p=author.canonical_parent(root=root);need(exact(p,prior['canonical_parent'])and exact(p,saved['canonical_parent']),'independently pinned selected113 parent')
 core=scout.unit_core(p);need(exact(core,prior['unit_core']),'literal independent six-unit core')
 free=p['polynomial_ledger']['free'];fixed=p['fixed_numerals'];d,co=scout.expand(core,free);weights=[int(v not in fixed)for v in free]
 degree=lambda f:max((sum(e*w for e,w in zip(mon,weights))for mon in f),default=-1)
 top=lambda f:{mon:c for mon,c in f.items()if sum(e*w for e,w in zip(mon,weights))==degree(f)}
 leaders=[top(d[port])for port in scout.PORTS];need([degree(d[port])for port in scout.PORTS]==[12,4,7,10,7,1],'all actual unit degrees')
 need([[[list(k),v]for k,v in sorted(f.items())]for f in leaders]==prior['unit_highest_polynomials'],'all actual uniform leading coefficients')
 def product(items):
  r=co(1)
  for item in items:r=scout.mul(r,item)
  return r
 square=lambda f:scout.mul(f,f)
 private=['tau_gap','ga','rho','j','h','alpha'];private_degrees=[2,2,2,2,1,1]
 expected_private=[co(1),square(d['a4m5']),square(d['a4m5']),product([square(d['i']),scout.powp(d['c'],6,co(1))]),{mon:-v for mon,v in d['UM'].items()},co(1)]
 for port,var,n,coefficient in zip(scout.PORTS,private,private_degrees,expected_private):
  polynomial=d[port];j=free.index(var)
  need(max(mon[j]for mon in polynomial)==n and all(not mon[free.index(other)]for mon in polynomial for other in private if other!=var),'exact private-coordinate degrees and disjoint supports')
  got={tuple(0 if k==j else e for k,e in enumerate(mon)):v for mon,v in polynomial.items()if mon[j]==n}
  need(got==coefficient,'nonzero private-coordinate coefficient establishes substitution injectivity')
 # Actual first norm, not just its advertised scalar expression.
 V=product([d['wn2'],square(d['sn2'])]);K=d['R10b'];T=scout.add(scout.mul(V,K),d['tau_gap'])
 need(scout.add(square(T),product([V,scout.add(V,co(1)),square(K)]),-1)==d['first_unit'],'literal first norm in the descent variables')
 small,smallco=scout.expand([],['V','T','k']);vv,tt,kk=[small[n]for n in('V','T','k')];dd=scout.mul(vv,scout.add(vv,smallco(1)));aa=scout.add(scout.mul(smallco(2),vv),smallco(1))
 knew=scout.add(scout.mul(aa,kk),scout.mul(smallco(2),tt),-1);tnew=scout.add(scout.mul(aa,tt),scout.mul(scout.mul(smallco(2),dd),kk),-1)
 need(scout.add(square(tnew),scout.mul(dd,square(knew)),-1)==scout.add(square(tt),scout.mul(dd,square(kk)),-1),'independent exact norm-preserving descent')
 allparts=[scout.canonical_partition(g)for g in scout.all_partitions(list(range(6)))];allowed=sorted([g for g in allparts if all(not(4 in block and 5 in block)for block in g)])
 strong=[g for g in allowed if all(len(set(block)&{0,4,5})<=1 for block in g)]
 need(len(set(json.dumps(g)for g in allparts))==203 and len(allowed)==151 and len(strong)==77,'independent canonical census')
 need(sorted(saved['all_set_partitions'])==sorted(allparts)and sorted(saved['admissible_partitions'])==allowed and sorted(saved['integer_certified_partitions'])==strong,'complete recorded partitions')
 counts=dict(full_sources=0,full_finalizers=0,residual_DAGs=0,live_gates=0,comparison_maps=0,raw_comparison_maps=0,unit_group_metadata=0,complete_leader_polynomials=0,uniform_nonzero_witnesses=0,whole_corrections=0,signed_cases=0,rational_cases=0,individual_residual_values=0,guards=0,copies=0,pin_rejections=0)
 forms=[];rng=random.Random(1062026);formal_corrections=set()
 bypart={json.dumps(f['packet']['partition']):f for f in saved['forms']}
 for group in allowed:
  c=author.build(group,root=root);form=bypart[json.dumps(group)];need(exact(c,form['packet']),'current canonical emitted source')
  expected=scout.candidate(p,core,group,True);I=Interner();a=I.run(c['polynomial_source'],free);b=I.run(expected['polynomial_source'],free)
  need(c['source'][:76]==core,'all76 independent core rows exactly equal')
  need(len(c['comparisons'])==len(expected['comparisons']),'residual multiplicity')
  def operand(env,x):return I.atom(('int',x))if type(x)is int else env[x]
  for old,new in zip(c['comparisons'],expected['comparisons']):
   need([operand(a,x)for x in old]==[operand(b,x)for x in new],'complete literal comparison operands');counts['residual_DAGs']+=1
  need(a[c['output']]==b[expected['output']],'entire paid finalizer DAG identical');counts['full_finalizers']+=1
  ports=[x for pair in c['comparisons']for x in pair];L=scout.ledger(c['polynomial_source'],free,[c['output']],fixed);C=scout.ledger(c['source'],free,ports,fixed)
  for field,v in L.items():need(exact(v,c['polynomial_ledger'][field]),'actual complete ledger metadata')
  for field,v in C.items():need(exact(v,c['certificate_ledger'][field]),'actual comparison ledger metadata')
  need((L['operations'],L['M'],L['A'])==(102+2*len(group),53,49+2*len(group)),'closed full count')
  need(exact(c['parameters'],p['parameters'])and exact(c['fixed_numerals'],fixed)and exact(c['witnesses'],p['witnesses'])and len(c['witnesses'])==24,'unchanged full coordinate interface')
  integer=group in strong
  for key,val in [('integer_zero_equivalence_certified',integer),('positive_zero_equivalent',True),('first_norm_descent_used',not integer),('same_supplied_coordinates',True),('full_polynomial_identity',len(group)==6)]:need(exact(c[key],val),'exact scoped theorem flags')
  need(c['zero_theorem_domain']==('integer'if integer else'positive_integer'),'current theorem domain')
  need(exact(c['active_interfaces'],dict(p['active_interfaces'],index='index_unit',bound='bound_unit')),'all active ports updated')
  expectedmap=[];kept=0
  for i in range(13):
   if i not in scout.OLD:expectedmap.append(dict(parent_index=i,new_index=kept,role='same_residual'));kept+=1
   else:
    j=scout.OLD.index(i);which=next(k for k,g in enumerate(group)if j in g);expectedmap.append(dict(parent_index=i,new_index=7+which,role='unit_group_member',old_residual_sign=-1 if i==3 else 1))
  need(exact(c['parent_comparison_map'],expectedmap),'complete current parent map');counts['comparison_maps']+=13
  raw=[]
  for record in p['original_raw_comparison_map']:
   z=copy.deepcopy(record)
   if z['new_index']is None:z['role']='historical_positive_definition'
   else:new=expectedmap[z['new_index']];z['new_index']=new['new_index'];z['role']=new['role']
   raw.append(z)
  need(exact(c['original_raw_comparison_map'],raw),'all original19rows mapped or explicitly historical');counts['raw_comparison_maps']+=len(raw)
  for j,g in enumerate(group):
   ports=[scout.PORTS[i]for i in g];meta=c['unit_groups'][j]
   need(meta['parent_indices']==[scout.OLD[i]for i in g]and meta['unit_ports']==ports and meta['comparison_index']==7+j and c['comparisons'][7+j]==[meta['product_port'],1],'literal group metadata');counts['unit_group_metadata']+=1
  diff=scout.correction(group);key=tuple(sorted(diff.items()));need(key not in formal_corrections,'distinct formal partition polynomials');formal_corrections.add(key);recorded=form['complete_correction'];need(recorded['unit_order']==scout.NAMES and recorded['coefficients']==[[list(m),v]for m,v in sorted(diff.items())],'entire formal offzero correction')
  groupdegrees=[sum(scout.DEGREES[i]for i in g)for g in group];D=max(groupdegrees);lead={};maxima=[]
  for j,g in enumerate(group):
   if groupdegrees[j]==D:lead=scout.add(lead,square(product(leaders[i]for i in g)));maxima.append(7+j)
  cert=form['degree_certificate'];need(cert['exact_degree']==c['exact_polynomial_degree']==2*D and cert['maximal_residual_indices']==maxima,'exact degree and every maximal group')
  need(cert['variables']==free and cert['degree_weights']==weights and cert['highest_homogeneous_polynomial']==[[list(m),v]for m,v in sorted(lead.items())],'entire uniform degree leader independent reconstruction');counts['complete_leader_polynomials']+=1
  need(cert['residual_exact_degrees']==[3,4,5,6,6,2,3]+groupdegrees,'all exact individual degrees')
  # Independently reproduce the proof of nonvanishing under arbitrary fixed
  # numeral choices: alpha appears only in Nb, and with coefficient one.
  deps=sorted({free[j]for mon in lead for j,e in enumerate(mon)if e and not weights[j]})
  need(set(deps)<={'Bm1','twice_cell_bits'}and cert['fixed_parameter_dependencies']==deps,'entire fixed-parameter dependence inventory')
  ai=free.index('alpha');highest_alpha=max(mon[ai]for mon in lead);need(highest_alpha in(0,2),'proper alpha coefficient')
  univariate={}
  for mon,coef in lead.items():
   if mon[ai]!=highest_alpha:continue
   need(mon[free.index('twice_cell_bits')]==0,'chosen coefficient independent of input constant')
   coef*=2**mon[free.index('tau_gap')];power=mon[free.index('Bm1')];univariate[power]=univariate.get(power,0)+coef
  univariate={k:v for k,v in univariate.items()if v};need(univariate and all(v>0 for v in univariate.values()),'strictly positive coefficient polynomial on every b>0 slice')
  need(cert['nonvanishing_alpha_coefficient_power']==highest_alpha and cert['positive_Bm1_witness']==[[k,v]for k,v in sorted(univariate.items())],'saved uniform witness');counts['uniform_nonzero_witnesses']+=1
  # Only the singleton partition is literally the same entire polynomial.
  # After canceling singleton blocks, largest nonsingleton weight exceeds
  # every participating individual weight, so its correction leader is a
  # nonzero sum of squares at a strictly higher degree.
  nonsingle=[g for g in group if len(g)>1]
  if nonsingle:
   maxw=max(sum(scout.DEGREES[i]for i in g)for g in nonsingle);oldmax=max(scout.DEGREES[i]for g in nonsingle for i in g);need(maxw>oldmax and diff,'actual nonzero correction has a strictly higher leader')
  else:need(not diff,'singleton exact same polynomial')
  for case in range(4):
   values={v:rng.randint(-2,3)if case<2 else rng.randint(1,4)for v in free};values.update(Bm1=15,Kconstant=163,twice_cell_bits=8,inner_bits=3,MC=2,MF=19)
   if case==2:values={v:Fraction(x,2)if v not in fixed else x for v,x in values.items()}
   old=scout.evaluate(p['polynomial_source'],values);new=scout.evaluate(c['polynomial_source'],values);units=[new[n]for n in scout.PORTS];delta=0
   for mon,coef in diff.items():
    for x,e in zip(units,mon):coef*=x**e
    delta+=coef
   need(new[c['output']]-old[p['output']]==delta,'actual entire source correction');counts['whole_corrections']+=1;counts['signed_cases']+=case<2;counts['rational_cases']+=case==2
   for i,pair in enumerate(p['comparisons']):
    val=lambda env,x:x if type(x)is int else env[x]
    oldres=val(old,pair[0])-val(old,pair[1])
    if i in scout.OLD:j=scout.OLD.index(i);need(oldres==(-1 if j==0 else 1)*(new[scout.PORTS[j]]-1),'actual unit versus old residual')
    else:now=c['comparisons'][expectedmap[i]['new_index']];need(oldres==val(new,now[0])-val(new,now[1]),'actual retained row')
    counts['individual_residual_values']+=1
   if case==3:need(author.evaluate(c,values,root=root)==new[c['output']],'guarded full public evaluation')
  counts['full_sources']+=1;counts['live_gates']+=L['operations'];forms.append(dict(partition=group,ledger=L,exact_degree=2*D,integer_zero_equivalence_certified=integer,correction_exact_degree=2*max(sum(scout.DEGREES[i]for i in g)for g in nonsingle)if nonsingle else None))
 counts['private_unit_coordinate_proofs']=6;counts['distinct_actual_polynomials']=len(formal_corrections);counts['first_norm_source_identity']=1;counts['descent_norm_identity']=1
 def frontier(points):return sorted({p for p in points if not any(q[0]<=p[0]and q[1]<=p[1]and q!=p for q in points)})
 positive=frontier([(f['ledger']['operations'],f['exact_degree'])for f in forms]);integer=frontier([(f['ledger']['operations'],f['exact_degree'])for f in forms if f['integer_zero_equivalence_certified']])
 need(positive==[(106,42),(108,28),(110,24)]and integer==[(108,30),(110,24)],'both independent exact frontiers')
 need(saved['family_frontier']==[list(x)for x in positive]and saved['integer_family_frontier']==[list(x)for x in integer],'saved frontiers')
 prior37=json.loads(blobs['complete_unit_partition_frontier109.json'])['known_union_frontier'];need(saved['known_union_frontier']==[list(x)for x in frontier([tuple(x)for x in prior37]+positive)],'exact frozen catalogue union')
 # Strict public validation, including canonical permutations and every source
 # domain flag. Copy checks and pins cover their independent entrypoints.
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('malformed public input accepted')
 for g in allparts:
  if g not in allowed:reject(lambda g=g:author.build(g,root=root))
 for g in(True,False,1,1.,'default',(),[],[[0],[1],[2],[3],[4]],[[0],[1],[2],[3],[4],[5],[5]],[[0],[1],[2],[3],[4],[True]],[[0],[1],[2],[3],[4],[5.]],[[1],[0],[2],[3],[4],[5]],[[0,5,2],[1,3,4]]):reject(lambda g=g:author.build(g,root=root))
 c=author.build(root=root);need(c['partition']==[[0,2,5],[1,3,4]],'default complete106/42')
 bads=[]
 for key in c:
  q=copy.deepcopy(c);q.pop(key);bads.append(q)
 for key in('source','polynomial_source','comparisons','unit_groups','partition','witnesses','parent_comparison_map'):
  q=copy.deepcopy(c);q[key]=tuple(q[key]);bads.append(q)
 for key in('positive_zero_equivalent','integer_zero_equivalence_certified','first_norm_descent_used','full_polynomial_identity','same_supplied_coordinates'):
  q=copy.deepcopy(c);q[key]=int(q[key]);bads.append(q)
 for key in('source','polynomial_source'):
  for i,row in enumerate(c[key]):
   for j in(2,3):
    if type(row[j])is int:
     for val in(float(row[j]),bool(row[j])):
      q=copy.deepcopy(c);q[key][i][j]=val;bads.append(q)
 q=copy.deepcopy(c);q['parent_comparison_map'][0]['new_index']=999;bads.append(q)
 q=copy.deepcopy(c);q['original_raw_comparison_map'][1]['new_index']=0;bads.append(q)
 q=copy.deepcopy(c);q['source'].append(['dead','+',1,0]);bads.append(q)
 for q in bads:reject(lambda q=q:author.checked(q,root=root))
 for q in(None,{},c,dict(p,comparisons=tuple(p['comparisons']))):reject(lambda q=q:author.rewrite(q,root=root))
 vals={v:1 for v in free}
 for value in(True,1.,Fraction(1,1),0,-1):
  v=dict(vals,x=value);reject(lambda v=v:author.evaluate(c,v,root=root))
 for mode in(0,1,None):reject(lambda mode=mode:author.evaluate(c,vals,signed=mode,root=root))
 v=dict(vals);v.pop('x');reject(lambda:author.evaluate(c,v,root=root));reject(lambda:author.evaluate(c,dict(vals,extra=0),root=root))
 q=copy.deepcopy(c);q['polynomial_source'][-1][-1]=0;reject(lambda:author.degree_certificate(q,root=root))
 for key in('source','polynomial_source','comparisons','partition','unit_groups','parent_comparison_map','historical_provenance','active_interfaces'):
  q=author.build(root=root);q[key].clear();need(exact(author.build(root=root),c),'defensive packet copy');counts['copies']+=1
 rows=author.polynomial_source(c,root=root);rows.clear();need(author.polynomial_source(c,root=root),'independent polynomial-source copy');counts['copies']+=1
 degree=author.degree_certificate(c,root=root);need(exact(degree,bypart[json.dumps(c['partition'])]['degree_certificate']),'guarded public degree certificate');degree['highest_homogeneous_polynomial'].clear();need(author.degree_certificate(c,root=root)['highest_homogeneous_polynomial'],'degree return is an independent copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='review_six_unit_')as td:
  root2=Path(td)/'Papers'/'research-wip'/'native-stream-queue';root2.mkdir(parents=True)
  for name,data in blobs.items():
   dest=root2/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
   if '/'in name:(root2/Path(name).name).write_bytes(data)
  need(exact(author.build(root=root2),c),'portable complete pinned inventory')
  for name,data in blobs.items():
   target=root2/name;target.write_bytes(data+b'\n');reject(lambda:author.build(root=root2));target.write_bytes(data);counts['pin_rejections']+=1
  counts['actual_relative_proof_pins_with_valid_fallback']=sum('/'in n for n in blobs)
 proc=subprocess.run([sys.executable,'-O',str(artifacts/'complete_six_unit_partition_frontier106.py'),'--help'],capture_output=True,text=True)
 need(proc.returncode!=0 and 'run without -O'in proc.stderr,'optimized interpreter rejects');counts['optimized_interpreter_guard']=1
 return dict(status='PASS_INDEPENDENT_SIX_UNIT151',review_source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,author_parent_pins=author.PINS,counts=counts,forms=forms,integer_frontier=[list(x)for x in integer],positive_frontier=[list(x)for x in positive],scope='All151 complete literal sources and finalizers, both scoped zero theorems, every actual exact highest form and typed public guards. Reviewer authored the separately pinned prior scout and reused its independent reconstruction, not the maintained author arithmetic implementation. No unrestricted grouping or global optimality claim.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.artifacts)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact independent saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
