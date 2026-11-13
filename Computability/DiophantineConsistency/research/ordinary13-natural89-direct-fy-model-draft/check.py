from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-natural89-direct-fy-model-draft')
fs=[p/'Natural89DirectFY.lean.src',p/'README.md',
Path('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),
Path('research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),
Path('research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src'),
Path('research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src'),
Path('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src'),
Path('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src'),
Path('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json')]
s=[f.read_text() for f in fs]
for x in ['theorem prototype_fy','EtaNaturalGraphStrongAuxDraft.ordinary_strong',
 'EtaNaturalStrongAuxDraft.f_positive_of_strong','EtaNaturalUnitBridgeDraft.signed_norms',
 'field_y','field_delta','field_f','natural_dvd_of_signed','theorem graph89_fy',
 'J88To89TransportDraft.zero_iff','Gamma87To88TransportDraft.zero_iff',
 'W86To87TransportDraft.zero_iff','EtaUnshift85TransportDraft.zero_iff',
 'Natural89Positive80TransportDraft.DirectFY K']:
 assert x in s[0],x
assert 'theorem natural_dvd_of_signed' in s[9]
G=json.loads(s[10]);r={row[0]:row for row in G['source']}
for row in [['f2','*','n_f','n_f'],['rho','-','f2',1],['Q','*','Delta','rho'],
 ['g72','-','g71','Q'],['y2','*','n_y','n_y'],['g81','-','y2','V2'],
 ['g82','*','Q','g81'],['Fa','-','y2','g82']]:assert r[row[0]]==row
rng=random.Random(89311);count=0
for t in range(600):
 v={key:rng.randrange(0,6) for key in G['witnesses']+G['fixed_numerals']}
 if t%2==0:v['n_y']=0
 e=v.copy()
 for name,op,l,r0 in G['source']:
  x=l if isinstance(l,int) else e[l];y=r0 if isinstance(r0,int) else e[r0]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 a=e['a'];D=3+4*a+a*a;f=v['n_f'];y=v['n_y'];z=e['V'];I=e['I']
 assert D>=3 and e['g72']==I*I-D*(f*f-1)
 assert e['Fa']==y*y-D*(f*f-1)*(y*y-z*z)
 if y==0:assert e['Fa']!=1
 if f==0:assert e['g72']!=0
 count+=1
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'exact_prototype_factor_controls':count,'lean_executed':False,
 'status':'unelaborated; r replacement, graph maps and providers remain open'},sort_keys=True,indent=2))
