#!/usr/bin/env python3
"""Independent full univariate-array evaluation for the fixed-coefficient diagonal."""
import gzip,hashlib,json,pathlib
D=pathlib.Path(__file__).resolve().parents[2];G=D/'research/trace74-mask-coordinate-probe/candidate.json';Q=D/'candidates/ten-positive-qcube-product-square/coefficients';P=1000000007
assert hashlib.sha256(G.read_bytes()).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
x=json.loads(G.read_text());v={n:[0,1] for n in x['witnesses']};degree={n:1 for n in x['witnesses']}
for n in x['fixed_numerals']:
 z=x['coefficient_binding']['ports'][n];packed=(Q/z['file']).read_bytes();raw=gzip.decompress(packed)
 assert hashlib.sha256(packed).hexdigest()==z['parent_gzip_sha256'] and hashlib.sha256(raw).hexdigest()==z['raw_sha256']
 v[n]=[int.from_bytes(raw,'little')%P];degree[n]=0
def get(y):return ([y%P],0) if type(y)==int else (v[y],degree[y])
for n,op,a,b in x['source']:
 A,da=get(a);B,db=get(b)
 if op=='*':
  out=[0]*(len(A)+len(B)-1)
  for i,ai in enumerate(A):
   for j,bj in enumerate(B):out[i+j]=(out[i+j]+ai*bj)%P
  degree[n]=da+db
 else:
  out=[0]*max(len(A),len(B));sgn=1 if op=='+' else -1
  for i,ai in enumerate(A):out[i]=(out[i]+ai)%P
  for i,bi in enumerate(B):out[i]=(out[i]+sgn*bi)%P
  degree[n]=max(da,db)
 v[n]=out
z=x['output'];assert degree[z]==402 and len(v[z])==403 and v[z][402]==217255545
print(json.dumps({'status':'PASS','graph_sha256':hashlib.sha256(G.read_bytes()).hexdigest(),'gate_upper_degree':degree[z],'diagonal_coefficient_t402_mod_1000000007':v[z][402],'scope':'external fixed-payload degree certificate, no Lean replay'},sort_keys=True))
