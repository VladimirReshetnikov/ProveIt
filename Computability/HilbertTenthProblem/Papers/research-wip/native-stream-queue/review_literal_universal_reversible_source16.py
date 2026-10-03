#!/usr/bin/env python3
"""Bounded Report16 intake: pinned data only; no archive code executes."""
import argparse,hashlib,io,itertools,json,math,subprocess,zipfile
from collections import Counter,defaultdict
from pathlib import Path
COMMIT='55d248dc504cff215684773123b3b03a8b8ebbe3'
ARCHIVE='docs/incoming/Literal_Universal_Reversible_Source_Package.zip'
ARCHIVE_SHA='20e6ee57b305ce7648fffa9c590c02807fecfb3fff8fc77885e0fdbab342be5d'
PREFIX='literal-reversible-source-release-20261003/'
MEMBERS={'source/PROOF.md': 'e1d40b0e5296dae92b903012ae36ee2fd344294b864d2a5a45190bfd3ac97914', 'source/README.md': 'ffb405b9e1a719cb4fd274743321cb12831a44c8af22f381defed9709b30341a', 'source/source.json': '38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a', 'source/build-stats.json': '367e75fb65181e876f797401cb3f496e9bf2c2acfaf438783b70e992ab616c2a', 'source/target-ledger.json': '2357630cdf2b538ca11cfd9e4fe2883c6cb13b211c8ad67c6f134b19c3cd4b63', 'source/loader.py': 'c371be6b8f7382fb351821f66c86591467195250e41759eb9240e00321e2be08', 'source/independent-macro-audit.md': '4f37302eb27c92af6537fe345ed2fc7f6ef80d12747447366abf57d16fecfc65', 'source/dependency/PROOF.md': '8511e3d09f9c69a73838329159b5e1e8e3a250d235252bdc54b9d46449db2b1b', 'source/dependency/virtual3.json': '24c771db50dc621068e470227802c2710a4531ce2e7ad3703a5cdb6b0543bbcf', 'source/dependency/tm_table.json': '0c6d8ae506f503e2783f6ed2ee68db4cde2f501b9864f376ab3773f86b59428a', 'source/compiler-reference/COMPILER_PROOF.md': '55ecb9c26bf0c2ce929c97187013171f8b8ec52ee30cb9a8703b41b1d106a4e8', 'primitive-certificates/PROOF.md': 'ad12a61e02abe49c121ea3a838381eb780fe1803f2126b453287801025c4d99d', 'primitive-certificates/example-source.json': '96321c1051285d90f2bec9a8915976b370400ae0826aed886c34e04ada4c468d', 'primitive-certificates/example-materialized.json': '9a431163c0e1d38f801a4dd6347d8c70e76111beb5c8ada47f708f968387f916', 'primitive-certificates/example-witness.json': 'de608e241c38f63330e179ca59898b6db7de816896be9966eb7984b297774080', 'primitive-certificates/universal-h1-ledger.json': '323b66434fa08aa404392ba05d12ceac35141286c14ebeaff1f43c15518eccf3'}
CURRENT={'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_parallel_particle_reports.md': '46990e5e8787dcc3d808d01e65c3e2b2bc7b815ce5d950b7424c96efe3cbca93', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/data/27-sparse-parallel-universal-receipt.json': '636a891f3c65ca3a895a3cbe9c12f4fcf5f82922b7f9cb77bfcf8914bb80f553', 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/17-startup-PROOF.md': '8a65456f53d759d4b58eafebbd0b201d45aa465b3f803c2ea011e5a76d4d62a9'}
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if isinstance(a,list):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def inspect_source(s):
 assert set(s)=={'schema','controls','start','halt','class_cut','branches'} and s['schema']=='reversible-two-counter-v1' and s['class_cut']==0
 controls=s['controls'];assert all(type(q)is str for q in controls);assert len(controls)==len(set(controls))==122622 and controls[0]==s['start']=='START' and s['halt']=='HALT'
 names=set();out={};incoming={};stats=Counter();per=defaultdict(Counter);out_rows=Counter();in_rows=Counter()
 classes=list(itertools.product(range(2),repeat=2))
 for e in s['branches']:
  assert set(e)=={'name','source','target','side','delta','guard'}
  assert type(e['name'])is str and e['name'] not in names;names.add(e['name'])
  q,t=e['source'],e['target'];assert q in set_controls and t in set_controls
  side=e['side'];delta=e['delta'];assert type(side)is int and side in [-1,1] and type(delta)is int and delta in [-1,0,1];j=int(side==1)
  guard=e['guard'];op=guard['op']
  if op=='true':assert guard=={'op':'true'}
  else:assert set(guard)=={'op','counter','value'} and op in ['eq','gt'] and type(guard['counter'])is int and guard['counter']in [0,1] and type(guard['value'])is int and guard['value']==0
  if delta==1:assert op=='true';kind='I'
  elif delta==-1:assert guard=={'op':'gt','counter':j,'value':0};kind='D'
  else:kind={'true':'A','eq':'Z','gt':'P'}[op]
  stats[kind]+=1
  if kind in ['I','D']:per['moving'][j]+=1
  if kind in ['Z','P']:per[kind][guard['counter']]+=1
  def enabled(v):return op=='true' or (v[guard['counter']]==0 if op=='eq' else v[guard['counter']]>0)
  domain=sum(1<<i for i,v in enumerate(classes)if enabled(v))
  # Exact interval partition {0},{1},{>=2}: for every permitted primitive,
  # the guard and zero/positive output class are constant on its nine cells.
  image=0
  for v in itertools.product(range(3),repeat=2):
   if not enabled(v):continue
   w=list(v);w[j]+=delta;assert min(w)>=0
   image|=1<<classes.index(tuple(int(x>0)for x in w))
  assert domain and image and not(out.get(q,0)&domain) and not(incoming.get(t,0)&image)
  out[q]=out.get(q,0)|domain;incoming[t]=incoming.get(t,0)|image;out_rows[q]+=1;in_rows[t]+=1
 assert s['start']not in incoming and s['halt']not in out
 assert stats=={'I':33436,'D':32630,'Z':23429,'P':52036,'A':30}
 return {'controls':len(controls),'branches':len(names),'primitive_counts':dict(stats),'moving_by_counter':[per['moving'][j]for j in [0,1]],'zero_tests_by_counter':[per['Z'][j]for j in [0,1]],'positive_tests_by_counter':[per['P'][j]for j in [0,1]],'max_outgoing_rows':max(out_rows.values()),'max_incoming_rows':max(in_rows.values()),'all_natural_partial_injection':True,'no_incoming_START':True,'no_outgoing_HALT':True}

def virtual_checks(v,tm):
 assert len(v['rows'])==528 and len(tm)==30 and tm['J1']is None and sum(x is None for x in tm.values())==1
 # Independent transcription of the supplied primary Table16 (c=0,b=1).
 pairs=[((0,'R','B'),(1,'R','A')),((1,'R','C'),(1,'R','A')),((0,'L','G'),(0,'L','E')),((0,'L','F'),(1,'L','E')),((1,'R','A'),(1,'L','D')),((1,'L','D'),(1,'L','D')),((0,'L','H'),(1,'L','G')),((1,'L','I'),(1,'L','G')),((0,'R','A'),(1,'L','J')),((1,'L','K'),None),((0,'R','L'),(1,'R','N')),((0,'R','M'),(1,'R','L')),((0,'L','B'),(1,'R','L')),((0,'L','C'),(0,'R','O')),((0,'R','N'),(1,'R','N'))]
 table={chr(65+i)+str(b):list(pair[b])if pair[b]is not None else None for i,pair in enumerate(pairs)for b in [0,1]};assert tm==table
 visits=set();cases=0;steps=0
 def step(q,a):
  visits.add(q);row=v['rows'][q];op,j,*targets=row
  if op=='ADD':a[j]+=1;return targets[0]
  assert op=='SUB'
  if a[j]:a[j]-=1;return targets[0]
  return targets[1]
 cuts=set(v['tm_cuts'].values())
 for key,transition in tm.items():
  if transition is None:continue
  write,direction,state=transition;j=1 if direction=='R' else 0
  for L,R in itertools.product([0,1,4],repeat=2):
   initial=[L,R,0];a=initial[:];q=v['tm_cuts'][key];count=0
   while True:
    q=step(q,a);count+=1;assert count<1000
    if q in cuts and a[2]==0:break
   Q,remainder=divmod(initial[j],2);wanted=initial[:];wanted[j]=Q;wanted[1-j]=2*initial[1-j]+write
   assert q==v['tm_cuts'][state+str(remainder)] and a==wanted and count==5*Q+remainder+7*initial[1-j]+write+4
   cases+=1;steps+=count
 for T in [0,1,7]:
  a=[2,3,T];q=v['entry'];count=0
  while q!=v['tm_cuts']['A0']:q=step(q,a);count+=1
  assert a==[2,3,0]and count==T+1
 return {'primary_table_cells':30,'TM_macro_cases':cases,'TM_literal_steps':steps,'visited_three_counter_rows':len(visits),'scratch_clear_cases':3,'scope':'Finite actual three-counter traces support, but do not replace, the all-input macro invariant proofs.'}

def geometry(m,p,a,J):
 D=2*m+4*p;S=2*D+2;B2=D+1;L=3*D+4;B3=4*D+5;Z=10*B3+10+2*J
 pair=4*p;triple=8*p*D+23*p+m;context=2*p+a
 return dict(m=m,p=p,a=a,J=J,D=D,S=S,B2=B2,L=L,B3=B3,Z=Z,pair_factors=pair,unguarded_triple_factors=triple,contextual_triple_factors=context,factors=pair+triple+context,radius=pair*(6*D+8)+triple*(24*D+32)+context*(Z+J+12*D+16),observer_length=3*D+3,particles=5,alphabet=[0,1])

def small_polynomial(p,w,source):
 assert len(p['variables'])==len(w)==46 and len(p['rows'])==42 and w[-1]==3115
 a=[0,0];state=source['start'];steps=clock=0;g=geometry(6,2,3,0)
 while state!=source['halt']:
  choices=[e for e in source['branches']if e['source']==state];assert len(choices)==1;e=choices[0];guard=e['guard'];j=int(e['side']==1)
  assert guard['op']=='true' or (a[guard['counter']]==0 if guard['op']=='eq' else a[guard['counter']]>0)
  clock+=1 if e['delta']==0 else 3+2*(g['Z']+a[j])+e['delta']-4*g['S']
  a[j]+=e['delta'];state=e['target'];steps+=1;assert min(a)>=0 and steps<=5
 assert steps==5 and clock==3115 and a==[0,0]
 expansion=Counter();degree=0
 for label,terms in p['rows']:
  value=0
  for c,monomial in terms:
   z=c
   for i in monomial:z*=w[i]
   value+=z
  assert value==0
  for c,x in terms:
   for d,y in terms:expansion[tuple(sorted(x+y))]+=c*d
 expansion={m:c for m,c in expansion.items()if c};saved={tuple(m):c for c,m in p['expanded_polynomial']}
 assert expansion==saved and len(saved)==1100 and max(map(len,saved))==4
 return {'natural_witnesses':46,'residuals':42,'collected_polynomial_monomials':1100,'exact_degree':4,'full_assignment_zero':True,'clock':3115}

def verify(repo):
 raw=subprocess.check_output(['git','-C',str(repo),'show',COMMIT+':'+ARCHIVE]);assert sha(raw)==ARCHIVE_SHA
 z=zipfile.ZipFile(io.BytesIO(raw));blobs={}
 for name,h in MEMBERS.items():blobs[name]=z.read(PREFIX+name);assert sha(blobs[name])==h
 current={}
 for name,h in CURRENT.items():current[name]=(repo/name).read_bytes();assert sha(current[name])==h
 get=lambda n:json.loads(blobs[n]);s=get('source/source.json')
 global set_controls
 set_controls=set(s['controls']);source=inspect_source(s);g=geometry(source['controls'],66066,75495,0);assert g==get('source/target-ledger.json')
 virtual=virtual_checks(get('source/dependency/virtual3.json'),get('source/dependency/tm_table.json'))
 tapes=['']+[''.join(x)for k in [1,2]for x in itertools.product('01',repeat=k)];loads=0
 for left,right in itertools.product(tapes,repeat=2):
  L=sum(int(v)*2**i for i,v in enumerate(left));R=sum(int(v)*2**i for i,v in enumerate(right));A=2**L*3**R
  decoded=[];residue=A
  for prime in [2,3]:
   val=0
   while residue%prime==0:residue//=prime;val+=1
   decoded.append(val)
  assert decoded==[L,R]and residue==1 and math.gcd(A,77)==1
  positions=sorted([-g['Z']-A,0,g['Z'],g['S'],g['S']+1]);assert len(set(positions))==5;loads+=1
 empty=sorted([-g['Z']-1,0,g['Z'],g['S'],g['S']+1]);assert empty==[-20380381,0,1019018,1019019,20380380]
 B=source['branches'];M=66066;NZ=23429;NP=52036
 core={'witness_slope':B+4,'square_slope':6+NZ,'square_intercept':1,'written_term_slope':3*B+M+NP+NZ+11,'degree_upper':4}
 assert core=={'witness_slope':141565,'square_slope':23435,'square_intercept':1,'written_term_slope':566225,'degree_upper':4}
 h1=get('primitive-certificates/universal-h1-ledger.json');assert h1['variables']==core['witness_slope']+1 and h1['squared_residual_slots']==core['square_slope']+3
 clock_slope=B+2*M;clock_intercept=1-M;assert h1['raw_residual_term_slots']==core['written_term_slope']+clock_slope+clock_intercept+B+1
 # The source's unique first step proves the published K=1 universal sample
 # is not an accepting witness, without traversing its enormous prologue.
 first=[r for r in s['branches']if r['source']=='START'];assert len(first)==1 and first[0]['target']!='HALT'and first[0]['guard']=={'op':'true'}
 parallel=json.loads(next(b for n,b in current.items()if n.endswith('27-sparse-parallel-universal-receipt.json')))
 assert parallel['ledger']['radius']==180*g['D']+258==91711698 and parallel['source_sha256']!='38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a'
 return {'status':'PASS','review_source_sha256':sha(Path(__file__).read_bytes()),'historical_commit':COMMIT,'archive':ARCHIVE,'archive_sha256':ARCHIVE_SHA,'member_pins':MEMBERS.copy(),'current_pins':CURRENT.copy(),'literal_source':source,'three_counter_checks':virtual,'ordered_binary_CA':g,'loader':{'finite_tape_cases':loads,'empty_positions':empty,'standard_input':'START(2^L*3^R,0)','extended_clean_input':'START(C*2^L*3^R*5^T,0), gcd(C,2310)=1'},'primitive_quartic':core,'clock_written_terms':{'slope':clock_slope,'intercept':clock_intercept},'small_complete_polynomial':small_polynomial(get('primitive-certificates/example-materialized.json'),get('primitive-certificates/example-witness.json'),get('primitive-certificates/example-source.json')),'parallel_comparison':{'radius':91711698,'actual_later_source_sha256':parallel['source_sha256'],'same_source_bytes':False},'scope':'Pinned bounded source/interface intake. Full literal source guard/image proof and exact numerical ledgers independently checked. Read macro proofs, but did not independently reconstruct all history/prime compilation tables, run archive code, traverse a universal computation, or construct an unbounded fixed-arity Diophantine compiler.'}

def main():
 if not __debug__:raise RuntimeError('Review assertions require unoptimized Python')
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.repo)
 assert exact(r,json.loads(json.dumps(r))),'type-exact roundtrip'
 if a.expect:assert exact(r,json.loads(a.expect.read_text())),'saved receipt'
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'source':r['literal_source'],'small_polynomial':r['small_complete_polynomial']},sort_keys=True))
if __name__=='__main__':main()
