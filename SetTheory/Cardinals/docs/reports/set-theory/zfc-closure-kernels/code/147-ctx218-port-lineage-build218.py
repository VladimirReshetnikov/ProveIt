#!/usr/bin/env python3
"""Exact deterministic construction from the independently certified direct188
219-state seed. This constructor proves byte reconstruction, not runtime.
Usage: python build218.py [output_directory]
"""
import hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
OUT=Path(sys.argv[1]) if len(sys.argv)>1 else HERE/'rebuilt'
OUT.mkdir(parents=True,exist_ok=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(T):return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n' for (q,b),(w,d,z) in sorted(T.items()))).encode()
def source_bytes(s):return (json.dumps(s,separators=(',',':'))+'\n').encode()
def right_rotate(s,paths):
 out=[]
 for p,op,a in s:
  matches=[x for x in paths if p.startswith(x)]
  assert len(matches)<=1
  if matches:
   x=matches[0];r=p[len(x):]
   if r.startswith('00'):r='0'+r[2:]
   elif r.startswith('01'):r='10'+r[2:]
   else:assert r.startswith('1');r='11'+r[1:]
   p=x+r
  out.append([p,op,a])
 out.sort();assert len({x[0]for x in out})==len(out)
 return out
raw=(HERE/'basis/direct188.tm').read_bytes();src=(HERE/'basis/direct188.sites.json').read_bytes()
assert sha(raw)=='65d2a8197cb10880220063a510802a25f26684ae76348c75f3c137d8e03ae956'
assert sha(src)=='9f3156afd95debd9961120d87104fbea551461612dfd67f3418076e08808773e'
T={}
for line in raw.decode().splitlines():
 if line.startswith('#')or not line.strip():continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),d,int(z))
s=json.loads(src);stages=[]
def record(name):
 table,source=encode(T),source_bytes(s)
 stages.append(dict(stage=name,table_sha256=sha(table),source_sha256=sha(source),states=len(T)//2))
 (OUT/(name+'.tm')).write_bytes(table);(OUT/(name+'.sites.json')).write_bytes(source)
record('direct188')
P188=['11101001001101111110','1110100100111001100110','111010010011101000010110','1110100100111010010','11101001001110101011010']
s=right_rotate(s,P188);T[188,0]=(0,'R',166);T[188,1]=(1,'R',12)
record('reuse12')
assert stages[-1]['table_sha256']=='923ef1382158d4ba10ea7d686a35c4bd6ea6f3d4d00572cbf536f6ba29a08f53'
assert stages[-1]['source_sha256']=='111c6ff95d165187e7be3d40ebe24c887f990bc1f249ec6fb41ae16e2f7fbe51'
P96=['111010010011011111001','11101001001110011001001','111010010011101000010101','11101001001110101011001']
s=right_rotate(s,P96);T[96,0]=(0,'R',98);T[96,1]=(1,'R',150)
record('reuse150')
T={(q,b):(w,d,85 if z==96 else z)for(q,b),(w,d,z)in T.items()if q!=96}
T[85,0]=(0,'R',98);T[85,1]=(1,'L',221)
record('candidate')
assert stages[-1]['table_sha256']=='4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651'
assert stages[-1]['source_sha256']=='1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe'
assert len(T)==436
inverse={102:301,120:302}
N={(inverse.get(q,q),b):(w,d,inverse.get(z,z))for(q,b),(w,d,z)in T.items()}
native=encode(N);assert sha(native)=='3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1'
(OUT/'candidate.native.tm').write_bytes(native)
receipt=dict(status='EXACT_DETERMINISTIC_RECONSTRUCTION_PASS',constructor_sha256=sha(Path(__file__).read_bytes()),stages=stages,native_sha256=sha(native),source_rotations=[dict(q=188,old_child=165,reuse=12,direction='right',paths=P188),dict(q=96,old_child=146,reuse=150,direction='right',paths=P96)],fold=dict(keep=85,drop=96,rows=[[0,'R',98],[1,'L',221]]),scope='Exact bytes only; source/control, startup and unbounded runtime proofs are separate.')
(OUT/'construction.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
