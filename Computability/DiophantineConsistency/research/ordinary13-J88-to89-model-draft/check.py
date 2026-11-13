from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys,tempfile,shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-J88-to89-model-draft')
fs=[p/'generate.py',p/'JShifted89Graph.lean.src',p/'J88To89Transport.lean.src',p/'README.md',
Path('research/ordinary13-natural-unit-product89/candidate.json'),
Path('research/ordinary13-natural-unit-product88/candidate.json'),
Path('research/ordinary13-natural-forced-gamma87/candidate.json'),
Path('research/ordinary13-natural-forced-w86/candidate.json'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),
Path('research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src'),
Path('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src'),
Path('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src'),
Path('research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src')]
s=[f.read_text() for f in fs]
with tempfile.TemporaryDirectory(prefix='J89-parent-') as d:
 root=Path(d)
 for f in [fs[0],fs[4]]:
  dst=root/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
 subprocess.run([sys.executable,'-I','-S','-B',str(fs[0])],cwd=root,check=True)
 assert (root/fs[1]).read_bytes()==fs[1].read_bytes()
g89,g88,g87,g86,g85=map(json.loads,s[4:9]);assert [len(g['source']) for g in (g89,g88,g87,g86,g85)]==[89,88,87,86,85]
for parent,child,name,var in [(g89,g88,'J','n_J'),(g88,g87,'gamma','n_gamma'),(g87,g86,'w','n_w'),(g86,g85,'eta','n_eta')]:
 assert [[var if x==name else x for x in row] for row in parent['source'] if row!=[name,'+',var,1]]==child['source']
assert g89['witnesses'][0]=='n_J'
for x in ['if i=0 then v i+1 else v i','if i=0 then v i-1 else v i','theorem J_positive',
 'Gamma87To88TransportDraft.zero_iff','W86To87TransportDraft.zero_iff',
 'EtaUnshift85TransportDraft.zero_iff','EtaNaturalJPositiveDraft.J_positive',
 '(h89 : PolynomialBridge','EtaUnshift85TransportDraft.ForcedEta K']:
 assert x in s[2],x
jproof=s[2].split('theorem J_positive',1)[1].split('theorem compact_no_zero_iff',1)[0]
assert 'ForcedEta' not in jproof and 'hbeta' not in jproof
P=1000000007
def calc(g,v):
 e={k:z%P for k,z in v.items()}
 for name,op,l,r in g['source']:
  x=l%P if isinstance(l,int) else e[l];y=r%P if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%P
 return e[g['output']]
rng=random.Random(88089)
for _ in range(400):
 v={k:rng.randrange(0,12) for k in g89['witnesses']+g89['fixed_numerals']}
 j=dict(v);j['n_J']+=1
 gm=dict(j);gm['n_gamma']+=1
 w=dict(gm);w['n_w']+=1
 e=dict(w);e['n_eta']+=1
 assert calc(g89,v)==calc(g88,j)==calc(g87,gm)==calc(g86,w)==calc(g85,e)
 assert e['n_J']==j['n_J'] and j['n_J']>0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'exact_J_gamma_w_eta_edits':True,'valuation_controls':400,'natural_port_K0_required':True,
 'J_proof_needs_no_beta_positivity_or_eta_forcing':True,'lean_executed':False,
 'status':'unelaborated; exact 89 bridge and provider provenance remain open'},sort_keys=True,indent=2))
