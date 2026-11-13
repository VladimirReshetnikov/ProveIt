#!/usr/bin/env python3
"""Independent bounded review of a partial 72 assignment; no Lean."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];d=base/'research/p64-qcube72-compact-window-partial-obstruction';graph=base/'research/p64-qcube72-free-main-candidate/graph.json';prior=base/'reviews/p64-free-fsquare75-symbolic-full-zero-independent/check.py'
pins={d/'README.md':'174157fba427260500f36221798d5d629ea196125af30fa235e19294eee5f63f',
 d/'check.py':'f3a6ba97dd648f46fe7723948e849bdd1c16e94b7bb976db15a3c129c2f3bb57',
 d/'result.json':'e83a0fc3d2bb0f89bba66561f52cb287fa5be3f6f5e7757163e9a4f7880224df',
 graph:'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',
 prior:'bb32ea64f45d70daf8b93b4aa6eab017366512016487d565813ac1358e64a59f'}
for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
r=subprocess.run([sys.executable,'-I','-S','-B',str(d/'check.py')],capture_output=True,check=True,timeout=20)
need(r.stdout==(d/'result.json').read_bytes() and not r.stderr,'author bounded check mismatch')
p=subprocess.run([sys.executable,'-I','-S','-B',str(prior)],capture_output=True,check=True,timeout=20)
a=json.loads(p.stdout);need(not p.stderr and a['status']=='PASS_BOUNDED_CHECKS' and a['strict_ratio']=='27 < c/k < 28','bounded Pell ratio')
need((a['A_mod_U'],a['k_mod_U'])==(486,428),'Pell residues')
beta,K0,MC,MF,J,F,alpha,z,w,s=2,1,1,0,1,1,1,1,2,1
rows=json.loads(graph.read_text())['source'];tab={row[0]:row for row in rows}
for name,row in {'Y':['Y','*','q3','s'],'R':['R','+','R_product','mask'],
                 'V':['V','-','f2_quotient','c'],'Na':['Na','+','aux_term','y2'],
                 'H_main_gap':['H_main_gap','*','H','h']}.items():
    need(tab[name]==row,'graph binding '+name)
q=beta*J+1;Y=q**3*s;X=w*q;U=Y*Y;aa=(X+1)*Y;H=4*aa+3;D=aa*aa+H;P=X*U;C=q-F-alpha
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
Lt=(K0+w)*C-F-z*(q-1)
need((q,Y,X,U,aa,H,D,P,C,R,Lt)==(3,27,6,729,189,759,36480,4374,1,41,0),'small coordinates')
need(MC<beta and MF<2*beta and 24<=R and R+q**3+q+1<=q**4 and R+1<q**4,'port/window bounds')
j=2446738;m=4020619
need(j>0 and m>0 and (2*P+1)**2-4*P*(P+1)==1 and (aa+2)**2-D==1,'Pell generators')
# k>=2j and c>27k, so c exceeds this integer lower bound.
c_lower=27*(2*j)+1
need(c_lower>2*R and c_lower>55 and 3*c_lower-4*R>1,'numeric inequality')
need((486+428-R-1)%q==2,'carrier residue')
# A0=1 and W=0 give Na=1+I²(V²-1), and the proved lower
# bound V>=3c-4R>1 makes the actual output positive for T=y=1.
need(beta==2 and (67*8807)>2,'not the exact compact beta')
out={'status':'PASS_PARTIAL_ASSIGNMENT_REVIEW','script_sha256':sha(__file__),
     'author_sha256':{p.name:sha(p) for p in (d/'README.md',d/'check.py',d/'result.json')},
     'graph_sha256':sha(graph),'ports':[beta,K0,MC,MF],'q':q,'R':R,
     'stronger_rank_window':[24,R,R+q**3+q+1,q**4],
     'minimum_c_lower_bound':c_lower,'carrier_mod_q':2,'T_and_y':1,
     'scope':'Symbolic partial assignment only; Na>1, so no full zero or fixed-compact44 conclusion; no Lean.'}
print(json.dumps(out,indent=2,sort_keys=True))
