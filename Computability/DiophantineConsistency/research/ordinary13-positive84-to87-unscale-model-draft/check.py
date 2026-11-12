from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-positive84-to87-unscale-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-positive84-to87-unscale-model-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
graphs=[]
for k in (84,87):
 p=Path('research/ordinary13-qcube-unscale84/candidate.json' if k==84 else 'research/ordinary13-aux-root87-36/candidate.json')
 g=json.loads(p.read_text());graphs.append(g);s=(D/f'PositiveUnscale{k}Graph.lean.src').read_text()
 assert len(g['source'])==k and len(g['witnesses'])==13
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in s
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in s
 for n,op,a,b in g['source']:assert f'  let {n} := {a} {op} {b}\n' in s
 assert '⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩' in s
assert graphs[0]['witnesses'][7]=='s' and graphs[1]['witnesses'][7]=='Y'
def ev(g,x,ports):
 v=dict(zip(g['witnesses'],x));v.update(zip(g['fixed_numerals'],ports))
 for n,op,a,b in g['source']:
  a=v[a] if isinstance(a,str) else a;b=v[b] if isinstance(b,str) else b
  v[n]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
 return v
for t in range(300):
 v=[(t*(i+3)+i*i+1)%7+1 for i in range(13)]
 ps=[(t*(j+2)+j)%5+1 for j in range(4)]
 s=(t%3)+1;q=1+v[0]*ps[0];v[7]=q**3*s
 a=ev(graphs[1],v,ps);w=v.copy();w[7]=s;w[8]=v[8]+s;b=ev(graphs[0],w,ps)
 assert a['Z']==q**3*b['Z'] and a['A0']==q**6*b['A0']
 for n in ('A1','Fa','g72'):assert a[n]==b[n]
 assert a['out']==q**12*b['A0']**2+b['A1']**2+(b['Fa']-1)**2+b['g72']**2
src=(D/'PositiveUnscale84To87.lean.src').read_text()
for token in ['theorem first_scale','theorem shared','theorem quotient_of_cut','positive_quotient_of_signed_norm','def ReverseRootCut','def ForwardNormBinding','theorem forward_of_norm_binding','theorem positive_zero_iff','(hf : ForwardGraphCut p) (hr : ReverseRootCut p)']:
 assert token in src,token
print(json.dumps({'author_audit_receipt_reproduces':True,'graph_literal_rows_checked':[84,87],'positive_scaled_graph_controls':300,'forward_uses_explicit_norm_binding':True,'reverse_root_cut_open':True,'lean_executed':False,'endpoint_bridge_proved':False},sort_keys=True,indent=2))
