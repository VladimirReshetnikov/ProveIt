#!/usr/bin/env python3
import pathlib,json,hashlib,gzip
D=pathlib.Path(__file__).resolve().parents[2];P=D/'con-zfc-diophantine-forms/72-congruence-sextic';S=D/'con-zfc-diophantine-forms/44-b4-sparse/native/coefficients';R=D/'research/p72-compact-port-path-restore'
def sha(x):return hashlib.sha256(x).hexdigest()
def h(p):return sha(pathlib.Path(p).read_bytes())
for f,pin in [('restore.py','beb51139327ed46693cbe20a70310d42af47bc9bd617a2b863c427564314d1c3'),('before.json','0e25a6dddc8ea5e730eff75e29ffd214b7dd54e493197e564d432ce0b5f00951'),('result.json','cdd61b4780d87c1f07282d0b7d732b2c8d9330f95c0c663f3670ffedf73db9b3')]:assert h(R/f)==pin
before=json.loads((R/'before.json').read_text());result=json.loads((R/'result.json').read_text());assert before['status']=='PASS_FOUR_ABSENT_VERIFIED_SOURCE_BYTES' and result['status']=='PASS_FOUR_FILES_RESTORED_AND_VERIFIED' and result['before_sha256']==h(R/'before.json') and before['ports']==result['ports']
bind=[]
for n,pin in [('positive13','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'),('positive14','f3ebbe2956482e2965c286d4a2cc648b99106e3e3859f1feb6cbebae820dc2ec')]:
 p=P/n/'ACTIVE_BINDING.json';assert h(p)==pin;d=json.loads(p.read_text());assert d['MF_convention'].startswith('Already shifted');bind.append((n,d))
out={}
for port in ['beta','K0','MC','MF']:
 vals=[]
 for n,b in bind:
  m=b['ports'][port];p=(P/n/m['path']).resolve();gz=p.read_bytes();raw=gzip.decompress(gz);assert gz==(S/p.name).read_bytes() and sha(gz)==m['sha256_gzip'] and sha(raw)==m['sha256_raw'] and len(raw)==m['raw_bytes'] and int.from_bytes(raw,'little').bit_length()==m['bits'] and raw[-1]!=0
  assert m['encoding']=='gzip of minimal unsigned little-endian bytes';vals.append((p,gz,m))
 assert vals[0][0]==vals[1][0] and vals[0][1]==vals[1][1]
 old=before['ports'][port];assert not old['exists_before'] and old['declared_path']==str(vals[0][0]) and old['source_path']==str((S/vals[0][0].name).resolve()) and old['gzip_sha256']==sha(vals[0][1])
 out[port]={'bits':vals[0][2]['bits'],'raw_bytes':vals[0][2]['raw_bytes'],'gzip_sha256':sha(vals[0][1])}
print(json.dumps({'status':'PASS','ports':out,'scope':'Observed prewrite record and current little-endian byte equality; no Lean file semantics or independent re-observation of past absence.'},indent=2,sort_keys=True))
