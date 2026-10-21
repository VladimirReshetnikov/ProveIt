"""Independent source-data audit; does not execute repository code or prove the endpoint."""
import json,re,hashlib
from pathlib import Path
D=Path(__file__).parent; U=D/'upstream'
s=(U/'KSource215Data.lean').read_text()
f=s[s.index('def fwd0'):s.index('def bwd0')];backward_text=s[s.index('def bwd0'):]
rx=r'\.leaf \((\d+), (\d+), \((-?\d+) : Int\), (\d+), (\d+)\)'
fwd=[tuple(map(int,x)) for x in re.findall(rx,f)]; bwd=[tuple(map(int,x)) for x in re.findall(rx,backward_text)]
assert len(fwd)==2240 and len(bwd)==2240
assert bwd==[(b,a,-z,j,k) for a,b,z,j,k in fwd]
r=(U/'Cert215Offsets.v').read_text()
rr=r'\(\[([^]]*)\], \[([^]]*)\], (-?\d+)%Z, (\d+)%N, (\d+)%N\)'
rows=[];paths=[]
def code(p):
 n=1
 for x in p:n=2*n+(x=='true')
 return n
for a,b,z,j,k in re.findall(rr,r):
 a=tuple(a.split(';')) if a else ();b=tuple(b.split(';')) if b else ()
 rows.append((code(a),code(b),int(z),int(j),int(k)));paths.extend([a,b])
assert rows==fwd
assert all(z==0 for a,b,z,j,k in fwd)
assert all(0<=j<2240 and 0<=k<2240 for a,b,z,j,k in fwd)
# Binary positive encoding has a leading sentinel 1, stripped by decode.
# This represents exactly the original lists, including all initial and final zero bits.
out='''(** EXPERIMENTAL DATA REFACTOR, NOT KERNEL-COMPILED HERE.
   The independent audit reconstructs all 2240 original certificate rows exactly.
   Existing OffsetBisim230 semantics and obligations are unchanged. *)
From Coq Require Import List NArith ZArith.
Import ListNotations.
Fixpoint decode_path_acc (p : positive) (acc : list bool) : list bool :=
  match p with
  | xH => acc
  | xO q => decode_path_acc q (false :: acc)
  | xI q => decode_path_acc q (true :: acc)
  end.
Definition decode_path (p : positive) : list bool := decode_path_acc p [].
Definition encoded215 : list (positive * positive * Z * N * N) := [\n'''
out+=';\n'.join(f'  ({a}%positive, {b}%positive, {z}%Z, {j}%N, {k}%N)' for a,b,z,j,k in fwd)+'\n].\n'
out+='Definition Cert215Compact : list (list bool * list bool * Z * N * N) :=\n  map (fun \'(a,b,z,j,k) => (decode_path a, decode_path b,z,j,k)) encoded215.\n'
(D/'Cert215Compact.v').write_text(out)
# Independently decode the output fields back to the input arrays.
encoded = re.findall(r'\((\d+)%positive, (\d+)%positive, (-?\d+)%Z, (\d+)%N, (\d+)%N\)',out)
assert len(encoded)==2240
for i,(aa,bb,zz,jj,kk) in enumerate(encoded):
 for side,c in enumerate((int(aa),int(bb))):
  bits=tuple('true' if x=='1' else 'false' for x in bin(c)[3:])
  assert bits==paths[2*i+side]
 assert (int(zz),int(jj),int(kk))==rows[i][2:]
j=json.loads((U/'completed.json').read_text())
def times(substr): return sum(x['seconds'] for n,x in j.items() if substr in n)
metrics={'pin':'c9dc79323429112c698100f3226a6e4d56c8b782','entries':len(fwd),'all_offsets_zero':True,'lean_reverse_exact_mirror':True,'lean_rocq_certificate_exact_match':True,'rocq_original_bytes':len(r.encode()),'rocq_compact_bytes':len(out.encode()),'lean_backward_data_bytes':len(backward_text.encode()),'max_path_length':max(map(len,paths)),'unique_paths':len(set(paths)), 'pairs_exceeding_128_bit_decoder':sum(max(a.bit_length()-1,b.bit_length()-1)>128 for a,b,z,j,k in fwd), 'upstream_rocq_declared_bytes':1499170, 'upstream_recorded_compile_seconds':{'total204':times(''),'source_forward16':times('KSource215FwdCheck'),'source_backward16':times('KSource215BwdCheck'),'sites10':times('KSites215'),'boot14':times('KBoot215')},'verification':'Independent Python data checks only. Proposed Lean/Rocq code not kernel-compiled here.'}
(D/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n'); print(json.dumps(metrics,indent=2))
