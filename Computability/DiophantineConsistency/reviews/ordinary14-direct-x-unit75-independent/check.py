#!/usr/bin/env python3
"""Independent graph and signed-ray review of direct-X unit 75; no Lean."""
import gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-direct-x-unit75'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'candidate.json','fd92751134276450eb62e186eaab024838196a1de1a684d175ed12385c646043');g=json.loads(s)
pin(A/'check.py','fb4a094f707d84c44c5efdfc9ff9c0938339c466a0557c8dcd753b2de748a511')
receipt=pin(A/'result.json','dd74f0d6189cd665a6a9fe360558e0607160a14f122ef3f87ffd3c6b1ba86916')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent external review is recorded in\n'
 b'`../../reviews/ordinary14-direct-x-unit75-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='612c3176d88b1aa5286ae33c1394cedb5746a95d862df093de0d7110c5974793'
p=json.loads(pin(D/'research/ordinary14-direct-roots79-56/candidate.json','fd4f02aef44ccd1b61227f66f65e7aa8a0f751fbc24b766a124ee31656b2c56e'))
assert g['witnesses']==p['witnesses'] and len(g['source'])==75
rows={a:(op,x,y) for a,op,x,y in g['source']}
assert rows['F0']==('-','g38','g40') and rows['F1']==('+',1,'A1') and rows['Fs']==('+',1,'g72')
assert rows['out']==('-','P01234',1)
assert 1*(1+2)-3==0 # h=1 scalar boundary can occur without the norm constraints.
# Authenticate the two bindings and all raw/gzipped port payloads.
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
mod=1000000007;fixed={}
for name,m in binding['ports'].items():
 assert b115['ports'][name]['sha256_raw']==m['sha256_raw'] and b115['ports'][name]['sha256_gzip']==m['sha256_gzip']
 z=(p72/m['path']).read_bytes();assert sha(z)==m['sha256_gzip'];raw=gzip.decompress(z)
 assert len(raw)==m['raw_bytes'] and sha(raw)==m['sha256_raw'];fixed[name]=int.from_bytes(raw,'little')%mod
v={x:[i+1,2*i+1] for i,x in enumerate(g['witnesses'])};v.update({k:[x] for k,x in fixed.items()})
def val(x):return [x%mod] if isinstance(x,int) else v[x]
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,sgn):return trim([((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%mod for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%mod
 return trim(z)
for name,op,x,y in g['source']:
 x=val(x);y=val(y);v[name]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
assert len(v['out'])-1==100 and v['out'][-1]==559992595

def replay(script,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check.py',receipt)
for name in ('ordinary14-direct-roots79-56-math-independent','ordinary14-shifted-guard87-calibration-math-independent'):
 p=D/'reviews'/name;replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'external conditional source replay and exact graph-degree review; no Lean',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'degree':100,'nonuniform_ray_leader_mod_1000000007':559992595},sort_keys=True,indent=2))
