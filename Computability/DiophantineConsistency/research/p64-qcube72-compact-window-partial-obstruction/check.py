#!/usr/bin/env python3
"""Finite premises for a partial 72 witness satisfying compact-type port bounds."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
pins={root/'research/p64-qcube72-free-main-candidate/graph.json':'875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806',root/'reviews/p64-free-fsquare75-symbolic-full-zero-independent/check.py':'bb32ea64f45d70daf8b93b4aa6eab017366512016487d565813ac1358e64a59f',root/'research/p64-qcube72-full-zero-mod-q-obstruction/README.md':'99b0da7530b0f7bbbaed76fd8c452b9791280babba8d8f2f82573552b842a860'}
for p,h in pins.items():
 if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+str(p))
prior=root/'reviews/p64-free-fsquare75-symbolic-full-zero-independent/check.py'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prior)],capture_output=True,text=True,timeout=20,check=True);a=json.loads(r.stdout)
if a['status']!='PASS_BOUNDED_CHECKS' or a['strict_ratio']!='27 < c/k < 28' or (a['A_mod_U'],a['k_mod_U'])!=(486,428):raise RuntimeError('Pell premise mismatch')
beta,K0,MC,MF,J,F,alpha,z,w,s=2,1,1,0,1,1,1,1,2,1
q=beta*J+1;Y=q**3*s;U=Y*Y;X=w*q;a0=(X+1)*Y;H=4*a0+3;D=a0*a0+H
C=q-F-alpha;R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
Lt=(K0+w)*C-F-z*(q-1)
if (q,Y,U,X,a0,H,D,C,R,Lt)!=(3,27,729,6,189,759,36480,1,41,0):raise RuntimeError('small graph arithmetic')
if not (MC<beta and MF<2*beta and R+1<q**4):raise RuntimeError('compact-type bounds')
j=2446738
if not 27*(2*j)>max(2*R,55):raise RuntimeError('Pell lower bound too small')
residue=(486+428-R-1)%q
if residue!=2:raise RuntimeError('rank residue')
# M=0 and W=0 follow from the exact Pell norms in README; with T=y=1,
# c>55 and f>=2 imply V>=3c-164>1 and Na=1+I²(V²-1)>1.
print(json.dumps({'status':'PASS_BOUNDED_PREMISES','ports':[beta,K0,MC,MF],'q':q,'R':R,'rank_window':str(R+1)+' < '+str(q**4),'first_main_ratio':a['strict_ratio'],'carrier_mod_q':residue,'auxiliary_status':'T=y=1 makes Na>1, so this is not a full zero','scope':'Bounded checks and exact symbolic norm argument only; no full-graph zero, compact44 conclusion or Lean theorem.'},sort_keys=True))
