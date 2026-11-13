from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-natural-unit-norm-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(D/'generate.py')])==(D/'generator-receipt.json').read_bytes()
old=Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src').read_text()
expected=old.replace('import EtaNaturalUnitGraph','import EtaZetaNaturalUnitGraph').replace('EtaNaturalUnitBridgeDraft','EtaZetaNaturalUnitBridgeDraft').replace('EtaNaturalUnitGraphDraft','EtaZetaNaturalUnitGraphDraft').replace('exact eta-natural\nprototype','exact eta/zeta-natural\nprototype')
assert (D/'EtaZetaNaturalUnitBridge.lean.src').read_text()==expected
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 q=1+b;Y=q**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4 != 3
G=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 d=dict(zip(G['witnesses'],v));d.update(zip(G['fixed_numerals'],p))
 for n,op,l,r in G['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for t in range(300):
 v=[(t*(i+3)+i*i+1)%8 for i in range(13)];v[10]=0;p=[(t*(j+3)+j)%9-4 for j in range(4)];a=ev(v,p)
 b=a['qm'];z=a['Z'];X=a['X'];Y=a['Y'];k=a['kbase'];ell=X*Y*(Y*k);delta=a['Delta'];f=a['n_f'];I=a['I'];D0=a['Dstar'];U=a['U'];c=a['c'];y=a['n_y'];vv=a['V']
 assert a['A0']==z*z-b*b*(1+ell*(ell+k))
 assert a['A1']==D0*D0-U*U*(1+delta*c*c)
 assert a['g72']==I*I-delta*(f*f-1)
 assert a['Fa']==y*y-delta*(f*f-1)*(y*y-vv*vv)
 assert a['out']==(1+a['A0'])*(1+a['A1'])*a['Fa']*(1+a['g72'])-1
print(json.dumps({'generator_receipt_reproduces':True,'exact_bridge_namespace_transcription':True,'first_pattern_mod4_cases':1024,'zeta_zero_graph_controls':300,'lean_executed':False,'graph_zero_units_proved':False},sort_keys=True,indent=2))
