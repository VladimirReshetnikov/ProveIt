#!/usr/bin/env python3
"""Fresh full unbounded certificates for the exact three K219 alternatives.

No generic case is filtered. All assertions must be enabled. Paths can be
supplied explicitly so the same checker runs in a portable archive.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, sys, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
ENGINE='c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER='0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
PHY=(6,2,0,4,3,7,8,5,1)
SPECS={
 'zero_terminal':dict(directory='machine/zero_terminal',table='b8e431c2543c71e9fdb86faf38c21c8c7aa9c61eb735b059966e6127bbe5d821',source='4a8994303330d0d8031929ace7f61737db86aee7beb9cbdf3ba593a0315bc4c2',steps=313845,cases=6175),
 'retagged':dict(directory='machine/retagged',
 table='54cb4e3e2f947172474676a478c331e5073fce612f3fc7b5c13742a8aba9363f',
 source='ba259d31c81ec18b3bb5be6f2162ed0373b9bfdad1b184c551c7c09737956b4a',steps=312707,cases=6167),
 'composed':dict(directory='machine/composed',
 table='4de59b14b068fac0071463b7237b740630ccaa7159d4cb4f097fc77a45bffb5c',
 source='7f58e08a02ec892e968e19a16825ca200e7b8bb4366efeb8df1cc25d63c8e890',steps=314043,cases=6175)}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def read_table(path):
 table={};headers=[]
 for line in Path(path).read_text().splitlines():
  if line.startswith('#! start '):headers.append(int(line.split()[-1]))
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
   assert(q,b)not in table and b in(0,1)and w in(0,1)and d in('L','R')
   table[q,b]=(w,1 if d=='R'else -1,z)
 assert headers==[0]
 return table

def startup(table,sites,spec,out):
 states={q for q,b in table};assert len(states)==219 and len(table)==438
 assert set(table)=={(q,b)for q in states for b in(0,1)}
 assert {z for w,d,z in table.values()}-states=={254}and 254 not in states
 order=[0];mp={0:0}
 for q in order:
  for b in(0,1):
   z=table[q,b][2]
   if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
 assert set(mp)==states;mp[254]=219
 dense={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in table.items()}
 data='#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(dense.items()))
 (out/'canonical.tm').write_text(data)
 # Sparse interpreter on literal labels, initially every cell zero.
 steps=spec['steps'];ones=set();q=h=0;visits=Counter()
 for _ in range(steps):
  b=int(h in ones);visits[q,b]+=1;w,d,q=table[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d
 # Independent dense interpreter on BFS-renamed labels. Its allocation
 # contains every location a machine could reach in this many steps.
 tape=bytearray(2*steps+3);origin=steps+1;head=origin;state=0;dv=Counter()
 for _ in range(steps):
  b=tape[head];dv[state,b]+=1;w,d,state=dense[state,b];tape[head]=w;head+=d
 logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
 for i,j in enumerate(PHY):physical[j]=logical[i]
 expected={-6,139};pos=140
 for v in physical+[1]*130:
  pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
 assert(q,h,ones)==(84,-5,expected)
 assert(state,head-origin,{i-origin for i,v in enumerate(tape)if v})==(mp[84],-5,expected)
 assert dv==Counter({(mp[q],b):v for(q,b),v in visits.items()})
 assert len(expected)==277
 result=dict(status='INDEPENDENT_EXACT_TABLE_STARTUP_CENSUS_PASS',table_sha256=spec['table'],source_sha256=spec['source'],
  states=219,rows=438,start=0,dispatch=84,halt=254,all_states_graph_reachable=True,canonical_sha256=sha(out/'canonical.tm'),
  normalized_to_canonical=mp,native_to_search={'301':102,'302':120},
  startup=dict(steps=steps,state=q,head=h,ones=sorted(ones),all_other_cells=0,logical_registers=logical,
  physical_registers=physical,spares=[1]*130,header=139,extra_gap=80,sparse_and_dense_agree=True),
  startup_row_counts=[[*k,v]for k,v in sorted(visits.items())])
 dump(out/'startup.json',result)
 return result

def runtime(table,sites,spec,out,vendor,mapping_path):
 assert sha(vendor/'symbolic_runtime.py')==ENGINE and sha(vendor/'independent_runtime.py')==HELPER
 sys.path.insert(0,str(vendor));import symbolic_runtime as rt
 original={int(k):v for k,v in json.loads(mapping_path.read_text()).items()}
 original[102]=1301;original[120]=1302
 mp={q:original.get(q,q+1000)for q in{q for q,b in table}|{254}}
 assert len(set(mp.values()))==len(mp)and(mp[0],mp[84],mp[254])==(95,96,254)
 legacy={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in table.items()}
 lemmas,blocks=rt.prove_blocks(legacy);print('Four exact-table universal block lemmas proved.',flush=True)
 started=time.monotonic();cases=[];rows=set()
 for index,site in enumerate(sites):
  for positive in((False,True)if site[1]=='CD'else(False,)):
   try:
    answer=rt.case(legacy,lemmas,site,positive)
    rows.update(answer.pop('rows'));answer.pop('trace')
    cases.append(dict(index=index,positive=positive,**answer))
   except Exception as e:
    failure=dict(status='GENERIC_PROOF_FAILED',table_sha256=spec['table'],source_sha256=spec['source'],
     index=index,positive=positive,site=site,reason=str(e),prior_proved_cases=len(cases),generic_cases_excluded=0)
    dump(out/'failure.json',failure);print('FAIL',json.dumps(failure),flush=True);raise
   if len(cases)%500==0:
    progress=dict(proved=len(cases),expected=spec['cases'],seconds=time.monotonic()-started)
    dump(out/'progress.json',progress);print('CHECKED',json.dumps(progress),flush=True)
 inverse={v:k for k,v in mp.items()}
 result=dict(status='ALL_GENERIC_PRIMITIVE_INTERFACES_PROVED',table_sha256=spec['table'],source_sha256=spec['source'],
  engine_sha256=ENGINE,helper_sha256=HELPER,mapping_file_sha256=sha(mapping_path),cases=len(cases),
  expected_cases=sum(2 if s[1]=='CD'else 1 for s in sites),failures=[],generic_cases_excluded=0,
  symbolic_steps=sum(x['symbolic_steps']for x in cases),seconds=time.monotonic()-started,block_schemas=blocks,
  directly_used_rows=sorted((inverse[q],b)for q,b in rows),mapping=mp,
  scope='Independent arbitrary natural primary values, gap, first spare and arbitrary finite remaining spare tail. Executable mathematical checking, not a proof-assistant kernel. No source guard or ad hoc exclusion filters generic cases.')
 dump(out/'cases.json',cases);dump(out/'runtime.json',result)
 print(json.dumps({k:v for k,v in result.items()if k not in('block_schemas','directly_used_rows','mapping','failures')}),flush=True)
 return result

def normalize(word):
 out=[]
 for bit,c,v in word:
  if out and out[-1][0]==bit:
   b,d,w=out.pop();out.append((b,d+c,w+v))
  else:out.append((bit,c,v))
 return out

def independent_blocks(table,stored):
 # Independently derive the symbolic one-block row trace. A variable run is
 # traversed by one exact self-loop, including zero repetitions.
 B=[(0,1,0),(1,1,1)];C=[(1,1,0),(0,1,0),(1,0,1)]
 specs=[(73,1,'B','B',[(0,1,0),(1,1,0),(1,0,1)]),
 (95,1,'B','C',[(0,1,0),(1,1,0),(1,0,1)]),
 (48,-1,'B','B',[(1,1,0),(1,0,1),(0,1,0)]),
 (112,-1,'C','B',[(1,0,1),(0,1,0),(1,1,0)])]
 assert len(stored)==4;reports=[]
 for rec,(entry,direction,before,after,tokens)in zip(stored,specs):
  assert(rec['entry'],rec['direction'],rec['before'],rec['after'])==(entry,direction,before,after)
  target=B if after=='B'else C;initial=B if before=='B'else C
  if direction==-1:target=list(reversed(target));initial=list(reversed(initial))
  assert normalize(tokens)==normalize(initial)
  q=entry;written=[];trace=[];constant=variable=0
  for bit,c,v in tokens:
   w,d,z=table[q,bit];assert d==direction;row=[q,bit,w,d,z]
   if v:
    assert(c,v)==(0,1)and z==q;trace.append(['unary',row,[0,0,1]+[0]*10])
   else:
    assert c==1;trace.append(['literal',row])
   q=z;written.append((w,c,v));constant+=c;variable+=v
  assert q==entry and(constant,variable)==(2,1)
  assert normalize(written)==normalize(target)
  assert rec['trace']==trace and rec['steps']=='v+2'and rec['arbitrary_contexts']is True
  reports.append(dict(entry=entry,direction=direction,before=before,after=after,trace=trace,duration=[2,1],arbitrary_exterior_untouched=True))
 return reports

def audit(table,sites,spec,out,vendor):
 rec=json.loads((out/'runtime.json').read_text());cases=json.loads((out/'cases.json').read_text())
 assert rec['status']=='ALL_GENERIC_PRIMITIVE_INTERFACES_PROVED'and rec['failures']==[]and rec['generic_cases_excluded']==0
 assert(rec['table_sha256'],rec['source_sha256'],rec['engine_sha256'],rec['helper_sha256'])==(spec['table'],spec['source'],ENGINE,HELPER)
 expected=[(i,p)for i,(_,op,a)in enumerate(sites)for p in((False,True)if op=='CD'else(False,))]
 assert len(expected)==len(cases)==rec['cases']==rec['expected_cases']==spec['cases']
 assert[(x['index'],x['positive'])for x in cases]==expected
 for x in cases:
  assert type(x['index'])is int and type(x['positive'])is bool
  assert type(x['symbolic_steps'])is int and 0<x['symbolic_steps']<4000
  assert len(x['duration'])==13 and all(type(v)is int and v>=0 for v in x['duration'])and x['duration'][0]>0
  assert len(x['motion'])==13 and all(type(v)is int for v in x['motion'])
  assert set(x['kinds'])<={'literal','unary','list'}and all(type(v)is int and v>0 for v in x['kinds'].values())
  assert sum(x['kinds'].values())==x['symbolic_steps']
 assert sum(x['symbolic_steps']for x in cases)==rec['symbolic_steps']
 mp={int(k):v for k,v in rec['mapping'].items()}
 assert set(mp)=={q for q,b in table}|{254}and len(set(mp.values()))==len(mp)
 assert(mp[0],mp[84],mp[254],mp[102],mp[120])==(95,96,254,1301,1302)
 legacy={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in table.items()}
 blocks=independent_blocks(legacy,rec['block_schemas'])
 assert rec['directly_used_rows']==[list(k)for k in sorted(table)]
 start=json.loads((out/'startup.json').read_text());s=start['startup']
 assert start['status']=='INDEPENDENT_EXACT_TABLE_STARTUP_CENSUS_PASS'
 assert(start['table_sha256'],start['source_sha256'])==(spec['table'],spec['source'])
 assert(start['states'],start['rows'],s['steps'],s['state'],s['head'])==(219,438,spec['steps'],84,-5)
 assert start['all_states_graph_reachable']and s['sparse_and_dense_agree']and s['all_other_cells']==0
 assert s['logical_registers']==[3,0,0,0,3,0,0,0,0]and s['spares']==[1]*130
 assert len(s['ones'])==277 and start['canonical_sha256']==sha(out/'canonical.tm')
 assert sha(vendor/'symbolic_runtime.py')==ENGINE and sha(vendor/'independent_runtime.py')==HELPER
 report=dict(status='INDEPENDENT_EXACT_TABLE_UNBOUNDED_STARTUP_AUDIT_PASS',working_states=219,transition_rows=438,
  table_sha256=spec['table'],source_sha256=spec['source'],generic_cases=spec['cases'],generic_cases_excluded=0,
  symbolic_steps=rec['symbolic_steps'],minimum_duration_constant=min(x['duration'][0]for x in cases),
  directly_used_rows=len(rec['directly_used_rows']),fresh_runtime_seconds=rec['seconds'],
  independently_rederived_block_schemas=blocks,checker_sha256=sha(Path(__file__)),
  hashes={name:sha(out/name)for name in['startup.json','runtime.json','cases.json','canonical.tm']},
  scope='Exact table/census/startup and fresh complete unbounded generic primitive refinement, with independent case/domain/row coverage, integrity and four-block audit. Source equivalence is a separate necessary certificate. Executable mathematical proof, not a proof-assistant kernel. This is 219 states, not <=218.')
 dump(out/'integrity.json',report)
 print('FINAL AUDIT',json.dumps({k:v for k,v in report.items()if k not in('hashes','independently_rederived_block_schemas')}),flush=True)
 return report

def main():
 assert __debug__ and not sys.flags.optimize
 ap=argparse.ArgumentParser();ap.add_argument('--variant',choices=list(SPECS),required=True)
 ap.add_argument('--table',type=Path);ap.add_argument('--source',type=Path)
 ap.add_argument('--vendor',type=Path,required=True)
 ap.add_argument('--mapping',type=Path,required=True)
 ap.add_argument('--out',type=Path,required=True);ap.add_argument('--audit-only',action='store_true');ap.add_argument('--preflight-only',action='store_true')
 a=ap.parse_args();spec=SPECS[a.variant];d=ROOT/spec['directory']
 table_path=a.table or d/'k219.native.tm';source_path=a.source or d/'sites.json';out=a.out or HERE/a.variant;out.mkdir(parents=True,exist_ok=True)
 assert sha(table_path)==spec['table']and sha(source_path)==spec['source']
 sites=json.loads(source_path.read_text());assert len(sites)==4744
 table=read_table(table_path)
 if not a.audit_only:
  startup(table,sites,spec,out);print('Whole blank tape: sparse/dense startup and census PASS.',flush=True)
  if a.preflight_only:return
  runtime(table,sites,spec,out,a.vendor,a.mapping)
 audit(table,sites,spec,out,a.vendor)
if __name__=='__main__':main()
