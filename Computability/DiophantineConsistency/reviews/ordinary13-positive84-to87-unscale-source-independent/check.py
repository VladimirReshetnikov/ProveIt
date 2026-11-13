from pathlib import Path
from hashlib import sha256
import json,sys,tempfile,shutil,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
p=P('research/ordinary13-positive84-to87-unscale-model-draft')
files=[p/'PositiveUnscale84Graph.lean.src',p/'PositiveUnscale87Graph.lean.src',p/'PositiveUnscale84To87.lean.src',p/'README.md',p/'generate.py',p/'check.py',p/'pins.json',p/'receipt.json',P('research/ordinary13-qcube-unscale84/candidate.json'),P('research/ordinary13-aux-root87-36/candidate.json'),P('research/ordinary13-qcube93-model-draft/Ordinary13QCube93Arithmetic.lean.src'),P('research/ordinary13-positive84-to87-unscale-model-audit/check.py'),P('research/ordinary13-positive84-to87-unscale-model-audit/receipt.json')]
s=[f.read_text() for f in files];g84,g87=map(json.loads,s[8:10]);assert [len(g['source']) for g in (g84,g87)]==[84,87]
with tempfile.TemporaryDirectory(prefix='unscale-review-') as d:
 root=P(d)
 for f in (files[4],files[8],files[9]):
  dest=root/f;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,dest)
 subprocess.run([sys.executable,'-I','-S','-B',str(files[4])],cwd=root,check=True)
 for f in files[:2]:assert (root/f).read_bytes()==f.read_bytes()
for g,source in [(g84,s[0]),(g87,s[1])]:
 for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in source
 for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in source
 for n,op,l,r in g['source']:assert f'  let {n} := {l} {op} {r}\n' in source,n
 assert '⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩' in source
assert g84['witnesses'][7]=='s' and g87['witnesses'][7]=='Y' and g84['witnesses'][8]==g87['witnesses'][8]=='r'
assert g84['witnesses'][:7]+g84['witnesses'][8:]==g87['witnesses'][:7]+g87['witnesses'][8:]
# Exact free-ring proof with h=q³, Y=h*s and r_new=r_old+s.
def add(x,y,sign=1):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+sign*n
 return {k:n for k,n in z.items() if n}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
one={(0,)*7:1};h={(1,0,0,0,0,0,0):1};b={(0,1,0,0,0,0,0):1};ell={(0,0,1,0,0,0,0):1};k={(0,0,0,1,0,0,0):1};r={(0,0,0,0,1,0,0):1};ss={(0,0,0,0,0,1,0):1};B={(0,0,0,0,0,0,1):1}
core=add(add(add(ell,k),r),mul(k,B),-1)
z87=add(add(mul(mul(h,b),core),mul(mul(h,ss),b)),mul(h,B),-1)
z84=add(mul(b,add(core,ss)),B,-1);rad=add(one,mul(ell,add(ell,k)))
a87=add(mul(z87,z87),mul(mul(mul(h,b),mul(h,b)),rad),-1);a84=add(mul(z84,z84),mul(mul(b,b),rad),-1)
assert z87==mul(h,z84) and a87==mul(mul(h,h),a84)
for token in ['def ScaledY','(ι (v 7) : DiffRing V)=q p v*q p v*q p v*ι s','theorem first_scale','update v s (v 8+s)','theorem shared','def ScaledFirstCut','theorem quotient_of_cut','positive_quotient_of_signed_norm','def ReverseRootCut','def ForwardGraphCut','def ForwardNormBinding','theorem forward_of_norm_binding','theorem positive_zero_iff']:
 assert token in s[2],token
reverse=s[2].split('def ReverseRootCut',1)[1].split('/--',1)[0]
assert reverse.index('PositiveUnscale84GraphDraft')<reverse.index('PositiveUnscale87GraphDraft') and '∃ y r : V, 0<y ∧ 0<r' in reverse
forward=s[2].split('def ForwardGraphCut',1)[1].split('/--',1)[0]
assert 'PositiveUnscale87GraphDraft' in forward and '∃ s : V, 0<s' in forward and 'q p v ≠ 0' in forward
norm=s[2].split('def ForwardNormBinding',1)[1].split('theorem forward_of_norm_binding',1)[0]
assert '∃ beta n : V, (p 0 : DiffRing V)=ι beta ∧ ScaledFirstCut' in norm
assert 'theorem positive_quotient_of_signed_norm' in s[10] and '(hy : 0<y)' in s[10]
assert 's is a model-natural element' in s[3] or 'model-natural' in s[3]
for a,b in ((files[5],files[7]),(files[11],files[12])):
 result=subprocess.run([sys.executable,'-I','-S','-B',str(a)],check=True,stdout=subprocess.PIPE);assert result.stdout==b.read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'literal_regeneration_and_rows':True,'q3_root_and_q6_residual_exact_polynomial_identities':True,'forward_and_reverse_cut_directions_checked':True,'signed_quotient_source_signature_checked':True,'author_and_audit_receipts_reproduced':True,'lean_executed':False,'status':'Unelaborated source review; explicit graph cuts, coherent providers and endpoint remain open.'},sort_keys=True,indent=2))
