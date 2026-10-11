"""Export every full single-X depth-five relation without discarding its top sector."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import array,gzip,hashlib,json,math,struct,sys
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1];V=B/'verification';C=B.parent/'reports/stieltjes-harmonic-resonance/continuations/exact-resonant-identities/certificates/cayley';sys.path.insert(0,str(C/'code'))
import verify_complete_cayley as M
P,R=M.P,M.R
for name,h in M.EXPECTED_SHA256.items():assert hashlib.sha256((C/name).read_bytes()).hexdigest()==h
probe_path=V/'S6-full-depth-five-probe.json.gz';summary=json.loads((V/'S6-full-depth-five-probe-summary.json').read_text());assert summary['status']=='PASS' and summary['tested_inputs']==1032 and hashlib.sha256(probe_path.read_bytes()).hexdigest()==summary['compressed_records_sha256']
with gzip.open(probe_path,'rt',encoding='utf-8') as f:probe=json.load(f)
old=V/'.scratch-real-orders/S6-intersection-integer-matrix.bin';oldmeta=json.loads((V/'S6-intersection-integer-matrix.json').read_text());assert hashlib.sha256(old.read_bytes()).hexdigest()==oldmeta['matrix_sha256']
f4=[w for w in product(range(5),repeat=7) if P.admissible(w) and P.depth(w)<=4 and P.parity(w)];top=[w for w in product(range(5),repeat=7) if P.admissible(w) and P.depth(w)==5 and P.parity(w)];coords=f4+top;index={w:i for i,w in enumerate(coords)};assert len(f4)==2546 and len(top)==6240 and len(coords)==8786
rows=[];den=1
for item in probe['rows']:
 row={index[tuple(w)]:Q(c) for w,c in item['projected_relation']};rows.append(row)
 for c in row.values():den=math.lcm(den,c.denominator)
assert sys.byteorder=='little' and array.array('q').itemsize==8
out=V/'.scratch-real-orders/S6-full-depth-five-matrix.bin';maxabs=0
with old.open('rb') as source,out.open('wb') as target:
 magic,nr,nc,oldD=struct.unpack('<4sIIQ',source.read(20));assert magic==b'S6M1' and nr==5155 and nc==2546 and oldD==384
 D=math.lcm(oldD,den);target.write(struct.pack('<4sIIQ',b'S6M1',nr+len(rows),len(coords),D));scale=D//oldD
 for j in range(nr):
  a=array.array('q');a.fromfile(source,nc);a=array.array('q',(c*scale for c in a));maxabs=max(maxabs,max(map(abs,a)));a.extend([0]*len(top));a.tofile(target)
 last=array.array('q');last.fromfile(source,nc);assert not source.read(1)
 for j,row in enumerate(rows):
  a=array.array('q',[0])*len(coords)
  for i,c in row.items():value=c.numerator*(D//c.denominator);assert -(1<<63)<value<(1<<63);a[i]=value;maxabs=max(maxabs,abs(value))
  a.tofile(target)
  if (j+1)%100==0:print('Full exact matrix new rows',j+1,'/',len(rows),flush=True)
 last=array.array('q',(c*scale for c in last));assert all(-(1<<63)<c<(1<<63) for c in last);maxabs=max(maxabs,max(map(abs,last)));last.extend([0]*len(top));last.tofile(target)
record=dict(rows=nr+len(rows),old_bounded_rows=nr,new_full_single_X_rows=len(rows),columns=len(coords),bounded_columns=len(f4),outside_columns=len(top),common_denominator=D,new_projected_denominator=den,maximum_absolute_integer=maxabs,maximum_includes_target=True,matrix_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),source_probe_sha256=summary['compressed_records_sha256'],old_matrix_sha256=oldmeta['matrix_sha256'],source_code_sha256=M.EXPECTED_SHA256,scope='All rational coefficients, including every depth-five component, are cleared by one common denominator. Old bounded rows and target are padded only with exact zero outside coordinates. Modular search is not a rational period certificate.')
(V/'S6-full-depth-five-matrix.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print('Full depth-five exact matrix',record['rows'],record['columns'],'denominator',D,'bytes',out.stat().st_size,flush=True)
