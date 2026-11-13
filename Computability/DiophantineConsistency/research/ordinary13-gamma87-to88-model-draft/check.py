from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys,tempfile,shutil
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-gamma87-to88-model-draft')
fs=[p/'generate.py',p/'GammaShifted88Graph.lean.src',p/'GammaNoExtraFacts.lean.src',p/'GammaPrototypePositiveEta.lean.src',p/'Gamma87To88Transport.lean.src',p/'README.md',
Path('research/ordinary13-natural-unit-product88/candidate.json'),
Path('research/ordinary13-natural-forced-gamma87/candidate.json'),
Path('research/ordinary13-natural-forced-w86/candidate.json'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),
Path('research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src'),
Path('research/ordinary13-residue90-gamma-model-draft/Residue90GammaModel.lean.src'),
Path('research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean'),
Path('research/ordinary13-eta-natural-norm-large-k-draft/EtaNaturalNormLargeK.lean.src'),
Path('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src'),
p/'GammaDirectRankGap.lean.src']
s=[f.read_text() for f in fs]
with tempfile.TemporaryDirectory(prefix='gamma88-parent-') as d:
 root=Path(d)
 for f in [fs[0],fs[6]]:
  dst=root/f;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dst)
 subprocess.run([sys.executable,'-I','-S','-B',str(fs[0])],cwd=root,check=True)
 assert (root/fs[1]).read_bytes()==fs[1].read_bytes()
g88,g87,g86,g85=map(json.loads,s[6:10]);assert [len(g['source']) for g in (g88,g87,g86,g85)]==[88,87,86,85]
for parent,child,name,var in [(g88,g87,'gamma','n_gamma'),(g87,g86,'w','n_w'),(g86,g85,'eta','n_eta')]:
 assert [[var if x==name else x for x in row] for row in parent['source'] if row!=[name,'+',var,1]]==child['source']
for x in ['GammaZeroNarrowDraft.gamma_zero_impossible U X Y (eta+zeta) eta R',
 'let P:=U*(X+a*c)+H*(U*(0:V)+R+1)','GammaDirectRankGapDraft.direct_rank_gap']:
 assert x in s[2],x
for x in ['(heta : 0<v 9)','EtaNaturalGraphEarlyIndexDraft.main_pair_norm','have hcarrier : v 12=0',
 'EtaNaturalGapRankDraft.compact_rank_window','EtaNaturalNormLargeKDraft']:
 assert x in s[3]+s[2],x
for x in ['if i=12 then v i+1 else v i','if i=12 then v i-1 else v i',
 'W86To87TransportDraft.zero_iff','EtaUnshift85TransportDraft.zero_iff',
 'GammaPrototypePositiveEtaDraft.gamma_positive','(h88 : PolynomialBridge',
 'EtaUnshift85TransportDraft.ForcedEta K']:
 assert x in s[4],x
assert 'theorem direct_rank_gap' in s[15] and 'by omega' not in s[15] and 'GammaDirectRankGap' in s[2]
assert 'ForcedEta' not in s[4].split('theorem gamma_positive',1)[1].split('theorem compact_no_zero_iff',1)[0]
P=1000000007
def calc(g,v):
 e={k:z%P for k,z in v.items()}
 for name,op,l,r in g['source']:
  x=l%P if isinstance(l,int) else e[l];y=r%P if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%P
 return e[g['output']]
rng=random.Random(87988)
for _ in range(400):
 v={k:rng.randrange(0,12) for k in g88['witnesses']+g88['fixed_numerals']}
 w=dict(v);w['n_gamma']+=1
 z=dict(w);z['n_w']+=1
 e=dict(z);e['n_eta']+=1
 assert calc(g88,v)==calc(g87,w)==calc(g86,z)==calc(g85,e)
 assert e['n_eta']>0 and e['n_gamma']==w['n_gamma']
for q in range(2,9):
 for X in range(1,5):
  for s0 in range(1,4):
   Y=q**3*s0; m=X*Y*Y; R=max(0,q**4-q**3-q-1);k=8*m+4
   assert R+X*Y*q+1<k and R+1<k and X<1+Y*k
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'exact_gamma_w_eta_edits':True,'valuation_controls':400,
 'source_no_extra_carrier_checked':True,'lean_executed':False,
 'status':'unelaborated; 88 parent bridge, 85 eta forcing and providers remain open'},sort_keys=True,indent=2))
