from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path
files=[p('research/ordinary13-natural89-direct-fy-model-draft/Natural89DirectFY.lean.src'),p('research/ordinary13-natural89-direct-fy-model-draft/README.md'),p('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),p('research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src'),p('research/ordinary13-eta-natural-strong-aux-adapter-draft/EtaNaturalStrongAux.lean.src'),p('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),p('research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src'),p('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean'),p('research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src'),p('research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src'),p('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src'),p('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src'),p('research/ordinary13-natural-unit-product89/candidate.json'),p('research/ordinary13-natural-unit-product88/candidate.json'),p('research/ordinary13-natural-forced-gamma87/candidate.json'),p('research/ordinary13-natural-forced-w86/candidate.json'),p('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in files];gs=list(map(json.loads,s[12:]));assert list(map(lambda g:len(g['source']),gs))==[89,88,87,86,85]
for idx,(name,var,pos) in enumerate([('J','n_J',0),('gamma','n_gamma',12),('w','n_w',6),('eta','n_eta',9)]):
 a,b=gs[idx:idx+2]
 assert a['witnesses']==b['witnesses'] and a['witnesses'][pos]==var
 assert [[var if x==name else x for x in row] for row in a['source'] if row!=[name,'+',var,1]]==b['source']
 assert f'if i={pos} then v i+1 else v i' in s[8+idx]
 assert pos not in (3,11)
r={row[0]:row for row in gs[-1]['source']}
for row in [['f2','*','n_f','n_f'],['rho','-','f2',1],['Q','*','Delta','rho'],['g72','-','g71','Q'],['y2','*','n_y','n_y'],['g81','-','y2','V2'],['g82','*','Q','g81'],['Fa','-','y2','g82']]: assert r[row[0]]==row
assert gs[-1]['witnesses'][3]=='n_f' and gs[-1]['witnesses'][11]=='n_y'
for i,needles in {0:['theorem prototype_fy','theorem graph89_fy','theorem directFY','EtaNaturalUnitBridgeDraft.signed_norms','natural_dvd_of_signed','EtaNaturalStrongAuxDraft.f_positive_of_strong','Natural89Positive80TransportDraft.DirectFY K'],2:['def DirectFY (K : ℕ)'],3:['theorem ordinary_strong','theorem field_f','theorem field_y'],4:['theorem f_positive_of_strong'],5:['theorem signed_norms','y*y-Delta*(f*f-1)*(y*y-vv*vv)=1'],6:['theorem field_delta','def delta'],7:['theorem natural_dvd_of_signed (a b : V)']}.items():
 for needle in needles: assert needle in s[i],needle
# Polynomial check at y=0 in Z[D,f,z]; dictionary is a complete expanded polynomial.
def add(a,b,sign=1):
 c=a.copy()
 for m,v in b.items():c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,x in a.items():
  for n,y in b.items():
   k=tuple(x+y for x,y in zip(m,n));c[k]=c.get(k,0)+x*y
 return {k:v for k,v in c.items() if v}
one={(0,0,0):1};D={(1,0,0):1};f={(0,1,0):1};z={(0,0,1):1};zero={}
aux=add(zero,mul(mul(D,add(mul(f,f),one,-1)),add(zero,mul(z,z),-1)),-1)
witness=mul(mul(D,add(mul(f,f),one,-1)),mul(z,z))
assert aux==witness
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'exact_four_graph_edits':True,'coordinates_3_and_11_preserved':True,'signed_aux_at_y_zero_exact_polynomial_identity':True,'reflection_source_signature_checked':True,'lean_executed':False,'status':'Unelaborated source-level review; graph-map providers, signed-norm dependencies, r replacement and endpoint remain open.'},sort_keys=True,indent=2))
