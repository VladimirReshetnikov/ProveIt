from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys,tempfile,shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-w86-to87-model-draft')
fs=[p/'generate.py',p/'WShifted87Graph.lean.src',p/'W86To87Transport.lean.src',p/'README.md',
Path('research/ordinary13-natural-forced-w86/candidate.json'),
Path('research/ordinary13-natural-forced-gamma87/candidate.json'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),
Path('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaShifted86Graph.lean.src'),
Path('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src'),
Path('research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src'),
Path('research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src')]
s=[f.read_text() for f in fs]
with tempfile.TemporaryDirectory(prefix='w87-parent-') as d:
 root=Path(d)
 for f in [fs[0],fs[5]]:
  dst=root/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
 subprocess.run([sys.executable,'-I','-S','-B',str(fs[0])],cwd=root,check=True)
 assert (root/fs[1]).read_bytes()==fs[1].read_bytes()
g86,g87,g85=map(json.loads,s[4:7])
assert len(g87['source'])==87 and len(g86['source'])==86 and len(g85['source'])==85
assert g87['witnesses']==g86['witnesses']==g85['witnesses'] and g87['witnesses'][6]=='n_w'
assert [[('n_w' if x=='w' else x) for x in row] for row in g87['source'] if row!=['w','+','n_w',1]]==g86['source']
assert [[('n_eta' if x=='eta' else x) for x in row] for row in g86['source'] if row!=['eta','+','n_eta',1]]==g85['source']
for x in ['if i=6 then v i+1 else v i','if i=6 then v i-1 else v i',
 'theorem w_positive','EtaUnshift85TransportDraft.zero_iff','EtaUnshift85TransportDraft.raiseEta',
 'EtaNaturalXPositiveDraft.witness_positive','ResidueCompactQBoundDraft.beta_at_least_46',
 'theorem compact_sameNoZero','(h87 : PolynomialBridge','EtaUnshift85TransportDraft.ForcedEta K']:
 assert x in s[2],x
assert 'ForcedEta' not in s[2].split('theorem w_positive',1)[1].split('theorem compact_no_zero_iff',1)[0]
P=1000000007
def calc(g,v):
 e={k:z%P for k,z in v.items()}
 for name,op,l,r in g['source']:
  x=l%P if isinstance(l,int) else e[l];y=r%P if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%P
 return e[g['output']]
rng=random.Random(6783)
for _ in range(500):
 v={k:rng.randrange(0,20) for k in g87['witnesses']+g87['fixed_numerals']}
 w=dict(v);w['n_w']+=1
 e=dict(w);e['n_eta']+=1
 assert calc(g87,v)==calc(g86,w)==calc(g85,e)
 assert w['n_w']>0 and w['n_w']-1==v['n_w'] and e['n_w']==w['n_w']
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'literal_rows':[87,86,85],'two_exact_affine_edits':True,'valuation_controls':500,
 'no_eta_forcing_in_w_positive':True,'lean_executed':False,
 'status':'unelaborated; exact 87 bridge, 85 forcing and provider provenance remain open'},sort_keys=True,indent=2))
