"""Export the exact projected S6 row matrix, with one common denominator."""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
from functools import lru_cache
import array,hashlib,json,math,pickle,struct,sys
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1];V=B/'verification';C=B.parent/'reports/stieltjes-harmonic-resonance/continuations/exact-resonant-identities/certificates/cayley';sys.path.insert(0,str(C/'code'))
import verify_complete_cayley as M
P,R=M.P,M.R
for name,h in M.EXPECTED_SHA256.items():assert hashlib.sha256((C/name).read_bytes()).hexdigest()==h
cache=pickle.loads((V/'.scratch-real-orders/S6-projector-images.pkl').read_bytes());assert cache['source_code_sha256']==M.EXPECTED_SHA256
coords=cache['coords'];index={w:i for i,w in enumerate(coords)};images=cache['images'];di=math.lcm(*(Q(c).denominator for row in images for c in row.values()));D=16*di
intimages=[{i:Q(c).numerator*(di//Q(c).denominator) for i,c in row.items()} for row in images]
@lru_cache(None)
def word(w):
 out=defaultdict(int)
 for a,c in M.change_basis(w).items():
  if not P.parity(a):continue
  c=Q(c);assert 16%c.denominator==0;factor=c.numerator*(16//c.denominator)
  for i,d in intimages[index[a]].items():out[i]+=factor*d
 return {i:c for i,c in out.items() if c}
def raw(row):
 out=defaultdict(int)
 for w,c in row:
  assert Q(c).denominator==1;c=int(c)
  for i,d in word(w).items():out[i]+=c*d
 return {i:c for i,c in out.items() if c}
family,counts=R.complete_family();old=sorted(family);probe=json.loads((V/'S6-depth-five-escape-probe.json').read_text());new=[]
for j,item in enumerate(probe['rows']):
 q={index[tuple(z['word'])]:Q(z['coefficient']) for z in item['projected_relation']};assert all(D%c.denominator==0 for c in q.values());new.append((j,{i:c.numerator*(D//c.denominator) for i,c in q.items()}))
out=V/'.scratch-real-orders/S6-enlarged-integer-matrix.bin';rowids=[];maxabs=0
with out.open('wb') as f:
 f.write(struct.pack('<4sIIQ',b'S6M1',len(old)+len(new),len(coords),D))
 for j,row in enumerate(old):
  q=raw(row);a=array.array('q',[0])*len(coords)
  for i,c in q.items():assert -(1<<63)<c<(1<<63);a[i]=c;maxabs=max(maxabs,abs(c))
  a.tofile(f);rowids.append(['old',j])
  if (j+1)%500==0:print('Exact integer matrix rows',j+1,'/',len(old),flush=True)
 for j,q in new:
  a=array.array('q',[0])*len(coords)
  for i,c in q.items():a[i]=c;maxabs=max(maxabs,abs(c))
  a.tofile(f);rowids.append(['new',j])
 target=raw(tuple(R.target().items()));a=array.array('q',[0])*len(coords)
 for i,c in target.items():assert -(1<<63)<c<(1<<63);a[i]=c;maxabs=max(maxabs,abs(c))
 a.tofile(f)
meta=dict(rows=len(rowids),columns=len(coords),common_denominator=D,projector_denominator=di,maximum_absolute_integer=maxabs,matrix_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),row_ids=rowids,old_row_counts=counts,source_code_sha256=M.EXPECTED_SHA256,probe_sha256=hashlib.sha256((V/'S6-depth-five-escape-probe.json').read_bytes()).hexdigest(),scope='Exact conjugation-odd projection followed by the full-Cayley retraction; every row and target is multiplied by the same positive integer denominator. The raw canonical rows represent imaginary components. Matrix data are search inputs, not a period identity certificate.')
(V/'.scratch-real-orders/S6-enlarged-integer-matrix.json').write_text(json.dumps(meta,indent=2)+'\n');print('Exact matrix written:',meta['rows'],meta['columns'],'denominator',D,'max integer',maxabs,flush=True)
