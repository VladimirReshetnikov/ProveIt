from pathlib import Path
from hashlib import sha256
import json,random,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS = {'research/ordinary13-qcube-main83/candidate.json': 'd19de596305c838c4b58f011a7fd233fedc4f7a7a87923cca60d00f46b408789', 'research/ordinary13-qcube-unscale84/candidate.json': '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77', 'research/ordinary13-positive81-to83-model-draft/PositiveCarrier83Graph.lean.src': '310288852701b446d7d708349c63e31a72b9e8cb215a8ba56ba66af0431cc6ce', 'research/ordinary13-positive81-to83-model-draft/Positive81To83Transport.lean.src': 'a01d62a2d5572c712c37bb8a4a933bea26f494b143f104bcbe484a58523f7ae0', 'research/ordinary14-modified-carrier-gamma-model-draft/CarrierGamma.lean': '5d8dc10ca61726a6c2b939c2d98a784fb06b702348b15fa657badf7545984d3a', 'research/ordinary13-positive83-to84-model-draft/Positive83To84Bridge.lean.src': '25c422df0ada61b60049e7ccc2cdfbb6ea1ab52060c40c9ba1d57f9fa37dac17', 'research/ordinary13-positive83-to84-model-draft/Positive83To84Transport.lean.src': '3797f24766c0842839c6c0dff4bc40cfc7a3e959edbdf578b5b16c2f918cea7a', 'research/ordinary13-positive83-to84-model-draft/PositiveUnscaled84Graph.lean.src': 'd2eb1fc077aac66c67a4c75f6b6a70792b6f0c7923f3ec952ea64d3ad7cf8740'}
for name,digest in PINS.items(): assert sha256(Path(name).read_bytes()).hexdigest()==digest,name
a,b=(json.loads(Path(p).read_text()) for p in list(PINS)[:2])
assert (len(a['source']),len(b['source']))==(83,84)
assert a['witnesses'][6]=='w' and b['witnesses'][6]=='X' and a['witnesses'][:6]+a['witnesses'][7:]==b['witnesses'][:6]+b['witnesses'][7:]
ra,rb=({r[0]:r for r in g['source']} for g in (a,b))
assert set(ra)-set(rb)=={'X'} and set(rb)-set(ra)=={'g55','g56'}
assert ra['X']==['X','*','q','w'] and rb['g55']==['g55','*','E','q'] and rb['g56']==['g56','+','g54','g55']
assert ra['shift']==['shift','-','g54','r0'] and rb['shift']==['shift','-','g56','r0']
assert all(ra[n]==rb[n] for n in ra.keys() & rb.keys() if n!='shift')
# Exact symbolic identity U*(gamma-w)+(X*Y)*q=U*gamma for X=q*w, U=Y*q².
def add(a,b,sgn=1):
 c=a.copy()
 for m,n in b.items(): c[m]=c.get(m,0)+sgn*n
 return {m:n for m,n in c.items() if n}
def mul(a,b):
 c={}
 for x,i in a.items():
  for y,j in b.items():
   k=tuple(u+v for u,v in zip(x,y));c[k]=c.get(k,0)+i*j
 return {k:n for k,n in c.items() if n}
q={(1,0,0,0):1};w={(0,1,0,0):1};Y={(0,0,1,0):1};gamma={(0,0,0,1):1}
assert add(mul(mul(Y,mul(q,q)),add(gamma,w,-1)),mul(mul(mul(q,w),Y),q))==mul(mul(Y,mul(q,q)),gamma)
# Verify generated 84 graph exactly, not only selected rows.
names=b['witnesses']+b['fixed_numerals']+[r[0] for r in b['source']]
assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n) for n in names)
lines=['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(b['witnesses'])]
lines+=['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(b['fixed_numerals'])]
lines+=['  let '+n+' := '+str(x)+' '+op+' '+str(y) for n,op,x,y in b['source']]
source=Path('research/ordinary13-positive83-to84-model-draft/PositiveUnscaled84Graph.lean.src').read_text()
assert source.split('def graph (p : Fin 4 → ℤ) : Graph :=\n',1)[1]=='\n'.join(lines)+'\n  ⟨A0,A1,Fa,g72,out⟩\nend PositiveUnscaled84GraphDraft\n'
# Sample full graph equality and positivity of both explicit maps.
def evalg(g,v,ports):
 e=dict(zip(g['witnesses'],v));e.update(zip(g['fixed_numerals'],ports))
 for n,op,x,y in g['source']:
  x=x if isinstance(x,int) else e[x];y=y if isinstance(y,int) else e[y]
  e[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return e
rng=random.Random(83084)
for _ in range(160):
 v=[rng.randrange(1,5) for _ in range(13)];ports=[rng.randrange(0,5) for _ in range(4)]
 v[12]+=v[6]; q=1+v[0]*ports[0]
 u=v.copy();u[6]=q*v[6];u[12]=v[12]-v[6]
 A,B=evalg(a,v,ports),evalg(b,u,ports)
 assert all(A[n]==B[n] for n in ['A0','A1','Fa','g72','out'])
 back=u.copy();back[6]=v[6];back[12]=u[12]+v[6]
 assert back==v and min(u)>0
s=Path('research/ordinary14-modified-carrier-gamma-model-draft/CarrierGamma.lean').read_text()
for term in ['theorem gamma_gt_from_modified_balance','(hc : c=ycoord R a) (hd : d=xcoord R a)','(hk : k=R+1+U*W)','w<gamma']:assert term in s
print(json.dumps({'sha256':PINS,'exact_graph_edits_and_84_transcription':True,'symbolic_carrier_identity':True,'sampled_full_graph_maps':160,'lean_executed':False,'status':'Conditional unelaborated source only; gamma calibration, q-divisibility, parent bridge and provider validation remain open.'},sort_keys=True,indent=2))
