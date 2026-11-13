from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys,tempfile,shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-positive81-to83-model-draft')
fs=[p/'generate.py',p/'PositiveCarrier83Graph.lean.src',p/'CarrierWitnessFacts.lean.src',
p/'Positive81To83Transport.lean.src',p/'README.md',
Path('research/ordinary13-qcube-main83/candidate.json'),
Path('research/ordinary13-residue-first81/candidate.json'),
Path('research/ordinary13-positive80-to81-model-draft/Positive80To81Transport.lean.src'),
Path('research/ordinary13-positive81-to83-model-gap-audit/README.md'),
Path('research/ordinary13-natural89-r-replacement-model-draft/Natural89RReplacement.lean.src')]
s=[f.read_text() for f in fs]
with tempfile.TemporaryDirectory(prefix='positive83-parent-') as d:
 root=Path(d)
 for f in [fs[0],fs[5]]:
  dst=root/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
 subprocess.run([sys.executable,'-I','-S','-B',str(fs[0])],cwd=root,check=True)
 assert (root/fs[1]).read_bytes()==fs[1].read_bytes()
a,b=map(json.loads,s[5:7]);assert len(a['source'])==83 and len(b['source'])==81
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals'] and a['witnesses'][8]=='r'
for x in ['positive_target_root','(hP : 0<P)','(ht : 0<t)','(hPt : P=b*t)','(htau : ell<tau)',
 'linear_combination ι b*ι k*hpR+ι b*htR-hPtR']:
 assert x in s[2],x
for x in ['theorem shared83_at','theorem shared81_at','theorem nonfirst_of_sum',
 'theorem zero81_to83','theorem zero83_to81','theorem prototype_zero_of81',
 'def CrossRootCut','(hc : CrossRootCut K)','(h83 : PolynomialBridge',
 'Positive80To81TransportDraft.native85']:
 assert x in s[3],x
P=1000000007
def calc(g,v):
 e={k:z%P for k,z in v.items()}
 for name,op,l,r in g['source']:
  x=l%P if isinstance(l,int) else e[l];y=r%P if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%P
 return e
rng=random.Random(8183)
for _ in range(600):
 vals={k:rng.randrange(1,12) for k in a['witnesses']};vals.update({k:rng.randrange(0,12) for k in a['fixed_numerals']})
 r=rng.randrange(1,20);alt=dict(vals);alt['r']=r
 g83,g81=calc(a,alt),calc(b,vals)
 for key in ['A1','Fa','g72']:assert g83[key]==g81[key]
 q=1+vals['J']*vals['beta'];F=vals['F'];C=q-F-vals['alpha'];X=q*vals['w'];K=vals['K0']
 Bp=C*(X+K)-F;B=C*(X+K*q)-F*q;assert B-Bp==(q-1)*(C*K-F)
for _ in range(500):
 b0=rng.randrange(1,10);t=rng.randrange(1,10);pp=b0*t;ell=rng.randrange(15);tau=ell+rng.randrange(1,10);k=rng.randrange(1,10)
 r=k*(pp-1)+t+(tau-ell)
 assert r>0 and b0*(ell+k+r-k*pp)-pp==b0*tau
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'shared_nonfirst_and_carrier_controls':600,'positive_target_root_controls':500,
 'cross_root_cut_and_83_bridge_explicit':True,'lean_executed':False,
 'status':'unelaborated; companion carrier and endpoint obligations remain open'},sort_keys=True,indent=2))
