from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-positive87-first-norm-binding-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/ordinary13-aux-root87-36/candidate.json').read_text()); rows={r[0]:r for r in g['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q3','*','q','q2'],['ell','*','E','kY'],['M','*','q3','qm'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['A0','-','g38','g42']]:assert rows[row[0]]==row

def evaluate(v,p):
 a=dict(zip(g['witnesses'],v));a.update(zip(g['fixed_numerals'],p))
 for n,op,x,y in g['source']:
  x=a[x] if isinstance(x,str) else x;y=a[y] if isinstance(y,str) else y
  a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return a
for t in range(500):
 v=[(t*(i+3)+i*i+1)%9 for i in range(13)];p=[(t*(j+2)+j)%7 for j in range(4)]
 a=evaluate(v,p);b=v[0]*p[0];h=(1+b)**3;k=v[9]+v[10];ell=v[6]*v[7]*(v[7]*k);N=1+ell*(ell+k);Bt=a['Bt']
 z=h*b*(ell+k+v[8]-k*Bt)+v[7]*b-h*Bt
 assert a['Z']==z and a['A0']==z*z-(h*b)**2*N
src=(D/'Positive87FirstNormBinding.lean.src').read_text()
for s in ['theorem root_form','ι (v 7)*ι (b p v)-ι (cubeScale (b p v))*bt p v','theorem first_form','theorem cut_of_zero','theorem forward_norm_binding','theorem forward_graph_cut','P72Root.cast_port']:
 assert s in src,s
print(json.dumps({'literal_rows_checked':True,'graph_root_norm_controls':500,'reverse_root_cut_open':True,'lean_executed':False},sort_keys=True,indent=2))
