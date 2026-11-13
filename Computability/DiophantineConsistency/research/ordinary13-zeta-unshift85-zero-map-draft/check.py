from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-zeta-unshift85-zero-map-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());probe=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
assert len(parent['source'])==len(probe['source'])==85
expected=[]
for row in parent['source']:
 if row==['k','+','kbase',1]:continue
 if row==['r0','-','kbase','R']:
  expected.extend([['r0base','-','kbase','R'],['r0','-','r0base',1]])
 else:expected.append([('kbase' if x=='k' else x) for x in row])
assert expected==probe['source']
# Exact local polynomial identities in Z[eta,zeta,R]:
def add(a,b,sgn=1):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+sgn*v
 return {k:v for k,v in c.items() if v}
one={(0,0,0):1}; eta={(1,0,0):1}; zeta={(0,1,0):1}; R={(0,0,1):1}
base=add(eta,zeta); raised=add(base,one)
assert raised==add(base,one)
assert add(add(raised,R,-1),one,-1)==add(base,R,-1)
def ev(g,v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p));mod=1000000007
 for n,op,l,r in g['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()%mod
 return d
for t in range(350):
 v=[(t*(i+3)+i*i+1)%11 for i in range(13)];p=[(t*(j+2)+j)%9-4 for j in range(4)]
 child=v.copy();child[10]+=1;a=ev(parent,v,p);b=ev(probe,child,p)
 for n in ('A0','A1','Fa','g72','out'):assert a[n]==b[n],n
src=(D/'ZetaUnshift85Transport.lean.src').read_text()
for token in ['def raiseZeta','if i=10 then v i+1 else v i','def lowerZeta','if i=10 then v i-1 else v i','theorem evaluation','def ForcedZeta','theorem compact_no_zero_iff','theorem compact_sameNoZero','(hparent : PolynomialBridge','theorem proposed_forcing','ZetaZeroCompactGraphDraft.zeta_positive','theorem native_equivalence']:
 assert token in src,token
print(json.dumps({'exact_row_rewrite_and_local_r0_identities':True,'parent_to_probe_controls':350,'same_operation_count_85':True,'parent_polynomial_bridge_explicit':True,'lean_executed':False,'endpoint_proved':False},sort_keys=True,indent=2))
