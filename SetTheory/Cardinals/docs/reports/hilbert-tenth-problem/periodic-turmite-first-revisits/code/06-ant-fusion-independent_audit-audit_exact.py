#!/usr/bin/env python3
"""Independent finite identities, closed ledger, and complete source reconstruction.
No upstream physical implementation or saved schedule is imported or executed.
"""
import collections, hashlib, importlib.util, json, pathlib, struct, sys, time
from array import array
sys.dont_write_bytecode=True
ROOT=pathlib.Path(__file__).resolve().parent
SNAP=ROOT/'candidate_snapshot'
BASE=pathlib.Path('/workspace/shared/ant-compression-report47-release-20261004')
S=576000; BW=600; N=960; HALF=288000
KINDS=('DUP','NAND','MOVE_LEFT','MOVE_RIGHT')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d): p.write_text(json.dumps(d,indent=2)+'\n')
def frozen_tree():return {str(p.relative_to(BASE)):digest(p) for p in sorted(BASE.rglob('*')) if p.is_file()}
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def authenticate():
 pins=json.loads((SNAP/'INPUT_PINS.json').read_text())
 for rel,row in pins.items():assert digest(SNAP/rel)==digest(pathlib.Path(row['source']))==row['sha256'],rel
 receipt=json.loads((SNAP/'fused-receipt.json').read_text())
 assert digest(SNAP/'fusion_source.py')==receipt['source_sha256']
 return receipt,pins

def profiles():
 p=BASE/'science/geometry/profiles';out={};q={}
 for name in ['H','B','F']:
  masks=[int(s,16) for s in json.loads((p/(name+'.masks.json')).read_text())['mask_hex_by_id']]
  ids=struct.unpack('<576000H',(p/(name+'.u16le')).read_bytes())
  out[name]=[masks[i] for i in ids]
 out['Hlow']=[h%2**25 for h in out['H']]
 out['Hhigh']=[h//2**25 for h in out['H']]
 out['first']=[h//2**25%2 for h in out['H']]
 for name in KINDS:
  d=json.loads((p/('Q_'+name+'.json')).read_text());ms=[tuple(int(v,16) for v in row) for row in d['signed_masks_by_id']]
  q[name]=[ms[i] for i in d['profile_id_by_dx']]
 return out,q

def partitions(profiles,receipt):
 result={};entry_count=0;allgroups={}
 for name,arr in profiles.items():
  result[name]={}
  for phase in [0,HALF]:
   supplied=receipt['block_array_identities'][name][str(phase)]['blocks']
   original=[None]*S;coverage=bytearray(N);grouping=[]
   for g in supplied:
    pos=g['positions']; assert pos==sorted(set(pos)) and pos
    ref=tuple(arr[(288650-phase-(BW*pos[0]+i))%S] for i in range(BW))
    assert hashlib.sha256(json.dumps(ref,separators=(',',':')).encode()).hexdigest()==g['mask_tuple_sha256']
    expanded=[]
    for start,length in g['runs']:
     assert length>0;expanded.extend(range(start,start+length))
    assert expanded==pos
    for k in pos:
     assert 0<=k<N and coverage[k]==0;coverage[k]=1
     original[k*BW:(k+1)*BW]=ref
    grouping.append((ref,tuple(pos)))
   assert all(coverage) and len(set(b for b,s in grouping))==len(grouping)
   # Direct inverse permutation of the coefficient map, distinct from block builder.
   for x,value in enumerate(arr):
    j=(288650-phase-x)%S
    assert original[j]==value,(name,phase,x);entry_count+=1
   # Verify half phase exactly rotates the fixed block index, no W identity.
   if phase:
    g0={b:set(seq) for b,seq in allgroups[name,0]}
    for b,seq in grouping: assert set(seq)=={(k-480)%N for k in g0[b]}
   allgroups[name,phase]=grouping;result[name][phase]=len(grouping)
 return {'status':'PASS_ALL_FROZEN_PROFILE_COEFFICIENTS','entries':entry_count,'group_counts':result},allgroups

def correction_exact(q):
 counts={};exponents=0
 for name,cols in q.items():
  assert len(cols)==1200
  bands=[]
  for lo,hi in [(0,51),(51,651),(651,1200)]:
   # Formal signed-mask coefficients. Zero extension is checked explicitly.
   b=len(bands);c=[(0,0)]*600
   for dx in range(lo,hi): c[50+600*b-dx]=cols[dx]
   assert all(c[r]==(cols[50+600*b-r] if lo<=50+600*b-r<hi else (0,0)) for r in range(600))
   bands.append(c)
  counts[name]=sum(p!=0 or m!=0 for p,m in cols)
  for phase in [0,HALF]:
   for b in range(3):
    slots=[(480-b-s-phase//600)%960 for s in range(957)]
    assert len(set(slots))==957 and len(set(range(960))-set(slots))==3
   for s in range(957):
    for dx in range(1200):
     b=0 if dx<51 else 1 if dx<651 else 2;r=50+600*b-dx
     k=(480-b-s-phase//600)%960
     x=(600*(s+1)+dx)%S;direct=(288650-phase-x)%S
     assert 600*k+r==direct and 0<=direct<S and bands[b][r]==cols[dx]
     exponents+=1
 return {'status':'PASS_FORMAL_CORRECTION_TERMS','term_identities_including_zero_terms':exponents,'all_Q_masks':4800,'nonzero_columns':counts}

def maximal_runs(seq):
 result=[];start=prev=seq[0]
 for x in seq[1:]:
  if x!=prev+1:result.append((start,prev-start+1));start=x
  prev=x
 result.append((start,prev-start+1));return result

def power_cost(n): return max(0,n.bit_length()-1+n.bit_count()-1)
def closed_counts(groups):
 req=[('H',HALF),('B',0),('B',HALF),('F',0),('F',HALF),('Hlow',0),('Hhigh',0),('first',0)]
 spatial=set();weights=set();numgroups=0
 for name,phase in req:
  for block,seq in groups[name,phase]:
   width={'Hlow':25,'Hhigh':375,'first':1}.get(name,400)
   coeff=tuple(('one' if v else 'zero') if name=='first' else ('zero' if v==0 else (width,v)) for v in block)
   spatial.add(coeff);weights.add(seq);numgroups+=1
 yruns=[maximal_runs(s) for s in weights]
 starts={0,1};lengths={1}
 for runs in yruns:
  for a,n in runs:starts.add(a);lengths.add(n)
 pM=sum(power_cost(k) for k in starts-{0,1})
 gM=sum(2*(n.bit_length()-1)+(n.bit_count()-1) for n in lengths-{1})
 gA=sum((n.bit_length()-1)+(n.bit_count()-1) for n in lengths-{1})
 runM=sum(a>0 and n>1 for runs in yruns for a,n in runs)
 runA=sum(len(r)-1 for r in yruns)
 M=len(spatial)*599+numgroups+pM+gM+runM
 A=len(spatial)*599+numgroups-len(req)+gA+runA
 assert (M,A)==(15911,15714)
 return dict(status='PASS_INDEPENDENT_CLOSED_LEDGER',block_horners=len(spatial),unique_weights=len(weights),group_products=numgroups,group_additions=numgroups-len(req),power_chain_M=pM,geometric_M=gM,geometric_A=gA,run_products=runM,run_additions=runA,fixed_block_M=M,fixed_block_A=A,Y_powers=sorted(starts),geometric_lengths=sorted(lengths))

class Ledger:
 """Independent validator/hash/count of actual arithmetic records."""
 def __init__(self,prior=None):
  self.n=self.M=self.A=0;self.digest=hashlib.sha256();self.known=set();self.records=collections.Counter();self.first=[]
  if prior:self.n,self.M,self.A=prior.n,prior.M,prior.A;self.digest=prior.digest.copy()
 def valid(self,v):
  if type(v)is int:assert 0<=v<self.n
  else:assert type(v)is str and (v in ['one','three'] or v in self.known)
 def gate(self,op,a,b):
  assert op in ['+','-','*'];self.valid(a);self.valid(b)
  i=self.n;line=f'{i}\t{op}\t{a}\t{b}\n';self.digest.update(line.encode())
  if i<3:self.first.append([i,op,a,b])
  self.n+=1
  if op=='*':self.M+=1
  else:self.A+=1
  return i
 def power(self,base,n):
  assert type(n)is int and n>=0
  if not n:return 'one'
  out=base
  for bit in format(n,'b')[1:]:
   out=self.gate('*',out,out)
   if bit=='1':out=self.gate('*',out,base)
  return out
 def metadata(self,row):
  self.records[row[0]]+=1;self.digest.update((json.dumps(row,separators=(',',':'))+'\n').encode())
 def receipt(self):return dict(M=self.M,A=self.A,total=self.n,sha256=self.digest.hexdigest())

class Reconstruct:
 """Independent old-main splice using fixed audited intervals, not recognition.
 All other old gate references are translated; removed interior uses are rejected.
 """
 def __init__(self,ledger,prepared,profiles,q,f,arity):
  self.d=ledger;self.p=prepared;self.profiles=profiles;self.q=q;self.f=f;self.arity=arity
  self.map=array('i');self.oldhash=hashlib.sha256();self.witnesses=[];self.raw=[];self.used=set();self.retained=0;self.removed=0;self.fusion_stats=None;self.final=None
  self.intervals=[(1264,1153262,'tile'),(1153262,2305260,'first')]
 def ref(self,v):
  if type(v)is int:
   assert 0<=v<len(self.map) and self.map[v]>=0,('invalid removed use',v)
   return self.map[v]
  if v.startswith('C:'):
   k=v[2:];assert k in self.p['labels'];self.used.add(k);return self.p['labels'][k]
  assert v in self.d.known;return v
 def write(self,line):
  self.oldhash.update(line.encode());r=json.loads(line)
  if type(r[0])is int:
   i,op,a,b=r;assert i==len(self.map)
   if i==1264:
    self.oldW=b;self.W=self.ref(b)
    n=self.d.n;fm=self.f.Fusion(self.d,self.W,self.p,self.profiles,self.q)
    self.tile,self.first,self.fusion_stats=fm.build();self.fused_gates=self.d.n-n
   interval=next(((lo,hi,name)for lo,hi,name in self.intervals if lo<=i<hi),None)
   if interval:
    lo,hi,name=interval;offset=i-lo;j=S-2-offset//2
    if offset%2==0:expected=[i,'*','C:'+name+':575999' if offset==0 else i-1,self.oldW]
    else:expected=[i,'+',i-1,'C:'+name+':'+str(j)]
    assert r==expected
    self.map.append((self.tile if name=='tile' else self.first) if i==hi-1 else -1);self.removed+=1
   else:self.map.append(self.d.gate(op,self.ref(a),self.ref(b)));self.retained+=1
  elif r[0]=='raw_positive':
   assert not self.d.known;self.raw=r[1];assert self.raw==(['RawLeft','RawRight']if self.arity==2 else ['RawInput']);self.d.known.update(self.raw);self.d.metadata(r)
  elif r[0]=='positive':
   assert r[1]not in self.d.known;self.d.known.add(r[1]);self.witnesses.append(r[1]);self.d.metadata(r)
  elif r[0]=='residual_pair':
   assert r[1]==self.d.records['residual_pair'];a,b=self.ref(r[2]),self.ref(r[3]);self.d.valid(a);self.d.valid(b);self.d.metadata([r[0],r[1],a,b,r[4]])
  elif r[0]=='eq':
   assert self.final is None;self.final=[self.ref(r[1]),self.ref(r[2])];assert self.final==[self.d.n-1,0];self.d.metadata(['eq',*self.final])
  else:raise ValueError(r)
  return len(line)
 def done(self,old,expected):
  assert self.oldhash.hexdigest()==old['source_sha256']==expected['old_main_source_sha256']
  assert self.witnesses==old['positive_witnesses']
  assert (self.d.M,self.d.A,self.d.n)==(expected['M'],expected['A'],expected['total'])
  assert self.d.digest.hexdigest()==expected['source_sha256']
  assert self.d.records=={'raw_positive':1,'positive':465 if self.arity==2 else 467,'residual_pair':285 if self.arity==2 else 286,'eq':1}
  assert self.removed==2303996 and self.retained==(3461 if self.arity==2 else 3471)
  assert len(self.used)==598 and self.used==set(self.p['labels']) and self.fused_gates==92107
  return dict(status='PASS_INDEPENDENT_RECONSTRUCTED_FULL_SOURCE',**self.d.receipt(),arity=self.arity,old_sha256=self.oldhash.hexdigest(),metadata_records=dict(self.d.records),unchanged_witness_list=True,retained_old_gates=self.retained,removed_old_gates=self.removed,fused_gates=self.fused_gates,final_operands=self.final,paid_constant_ports=len(self.used),no_removed_intermediate_used=True,unbound_coefficients=0)

def main():
 assert __debug__
 before=frozen_tree();dump(ROOT/'frozen-before.json',before)
 receipt,pins=authenticate();ps,q=profiles();f=module('audit_candidate_fusion',SNAP/'fusion_source.py')
 # These audits establish exact data identities before any modular evaluation.
 result={'candidate_sha256':digest(SNAP/'fusion_source.py'),'generic_proof_sha256':digest(ROOT/'GENERIC_PROOF.md'),'authenticated_input_files':len(pins)}
 result['blocks'],groups=partitions(ps,receipt);print('All frozen fixed coefficient arrays: PASS',flush=True)
 result['corrections']=correction_exact(q);print('All formal correction terms: PASS',flush=True)
 result['closed_counts']=closed_counts(groups);dump(ROOT/'finite-identities.json',result)
 d=Ledger();oc=module('audit_owned_occurrence',SNAP/'owned_report47/occurrence_compiler.py')
 prepared=f.prepare(d,oc,ps,q)
 assert d.first[0]==[0,'-','one','one'];assert d.receipt()==receipt['prefix'];assert prepared['stages']==receipt['prefix_stages']
 result['prefix']=d.receipt();print('Full actual constant prefix: PASS',d.receipt(),flush=True)
 old=module('audit_owned_main',SNAP/'owned_report44/merged_source.py');result['full_sources']={}
 for arity in [2,1]:
  l=Ledger(d);adapter=Reconstruct(l,prepared,ps,q,f,arity);r=old.build(stream=adapter,arity=arity)
  result['full_sources'][arity]=adapter.done(r,receipt['joins'][str(arity)])
  print('Independent complete-source splice: PASS',arity,l.receipt(),flush=True)
 after=frozen_tree();assert before==after;dump(ROOT/'frozen-after.json',after)
 result['frozen_files_unchanged']=len(before);result['status']='PASS_INDEPENDENT_EXACT_FUSION_AUDIT';result['audit_script_sha256']=digest(pathlib.Path(__file__))
 dump(ROOT/'audit-receipt.json',result)
 print(result['status'],flush=True)
if __name__=='__main__':main()
