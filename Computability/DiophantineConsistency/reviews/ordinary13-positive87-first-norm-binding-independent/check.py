from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path;p=P('research/ordinary13-positive87-first-norm-binding-draft');u=P('research/ordinary13-positive84-to87-unscale-model-draft')
files=[p/'Positive87FirstNormBinding.lean.src',p/'README.md',p/'check.py',p/'pins.json',p/'receipt.json',u/'PositiveUnscale87Graph.lean.src',u/'PositiveUnscale84To87.lean.src',P('research/ordinary13-aux-root87-36/candidate.json'),P('research/ordinary13-qcube93-model-draft/Ordinary13QCube93Arithmetic.lean.src'),P('Lean/DiophantineConsistency/Compact44/P72Root.lean')]
s=[f.read_text() for f in files];g=json.loads(s[7]);assert len(g['source'])==87 and len(g['witnesses'])==13
rows={r[0]:r for r in g['source']}
for row in [['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['E','*','X','Y'],['k','+','eta','zeta'],['kY','*','Y','k'],['ell','*','E','kY'],['M','*','q3','qm'],['g30','+','ell','k'],['g31','+','g30','r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','M','folded_g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g38','*','Z','Z'],['g39','*','M','M'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42']]:assert rows[row[0]]==row
for name,op,l,r in rows.values():assert f'  let {name} := {l} {op} {r}\n' in s[5]
assert '⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩' in s[5]
# Exact free-ring polynomial computation for the specified first-root cut.
def add(x,y,sgn=1):
 z=x.copy()
 for k,n in y.items():z[k]=z.get(k,0)+sgn*n
 return {k:n for k,n in z.items() if n}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {k:n for k,n in z.items() if n}
one={(0,)*6:1};b={(1,0,0,0,0,0):1};ell={(0,1,0,0,0,0):1};k={(0,0,1,0,0,0):1};r={(0,0,0,1,0,0):1};Y={(0,0,0,0,1,0):1};Bt={(0,0,0,0,0,1):1}
q=add(one,b);h=mul(q,mul(q,q));M=mul(h,b);core=add(add(add(ell,k),r),mul(k,Bt),-1)
env={'qm':b,'q':q,'q2':mul(q,q),'q3':h,'ell':ell,'k':k,'r':r,'Y':Y,'Bt':Bt}
for name in ['M','g30','g31','folded_kBt','folded_g31','g32','g33','g34','folded_q3Bt','Z','g38','g39','g40','g41','g42','A0']:
 _,op,l,r0=rows[name];x=one if l==1 else env[l];y=one if r0==1 else env[r0]
 env[name]={'+':lambda:add(x,y),'-':lambda:add(x,y,-1),'*':lambda:mul(x,y)}[op]()
z=add(add(mul(mul(h,b),core),mul(Y,b)),mul(h,Bt),-1)
rad=add(one,mul(ell,add(ell,k)))
assert env['Z']==z
assert env['A0']==add(mul(z,z),mul(mul(mul(h,b),mul(h,b)),rad),-1)
for n in ['def intPorts (p : Fin 4 → ℕ)','def b (p : Fin 4 → ℕ)','def ell (v : Fin 13 → V)',
 'def radicand (v : Fin 13 → V) : V := 1+ell v*(ell v+k v)',
 'theorem root_form','theorem first_form','theorem cut_of_zero','ScaledFirstCut (intPorts p) v (p 0:V) (radicand v)',
 'theorem forward_norm_binding (p : Fin 4 → ℕ) : ForwardNormBinding (intPorts p)',
 'P72Root.cast_port (V:=V) p 0','theorem forward_graph_cut (p : Fin 4 → ℕ)']:
 assert n in s[0],n
for n in ['def ScaledFirstCut','def ForwardNormBinding','theorem forward_of_norm_binding','theorem squares_zero'] :assert n in s[6],n
assert 'theorem positive_quotient_of_signed_norm (b y n : V) (hy : 0<y)' in s[8]
assert 'theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4)' in s[9]
assert 'PositiveUnscale84GraphDraft.graph' not in s[0] and 'ReverseRootCut' not in s[0]
res=subprocess.run([sys.executable,'-I','-S','-B',str(files[2])],check=True,stdout=subprocess.PIPE);assert res.stdout==files[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'exact_graph_first_root_rows_checked':True,'root_and_first_norm_polynomial_identities':True,'natural_port_and_quotient_signatures_checked':True,'author_receipt_reproduced':True,'lean_executed':False,'scope':'Source-only root/norm binding review; imported graph proof, quotient, providers, reverse cut and endpoint remain unelaborated.'},sort_keys=True,indent=2))
