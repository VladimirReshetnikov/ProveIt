#!/usr/bin/env python3
"""Independent direct 85 P72 source binder review; no Lean invocation."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-p72-exact-indices-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'P72ExactIndices85.lean','a7e058541155787edeca4b42e28000799a4befad24d9a973072669320f3d6855').decode()
pin(A/'check_source.py','7f821547f2f2bd888f71ffffca1cae644127d143cfb17376288833462c87ac1b')
receipt=pin(A/'observation.json','04bd94827fb1b4d661573d52c2186886898b7ae884ed5f1de909fa2f127dd4c4')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-p72-exact-indices-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='9bba08b747c8ff1541684aa22d8f99620b8629aa60ebbff5d898a0587c4f1ba9'
for path,h in {
 'research/ordinary14-85-p72-first-inputs-draft/P72FirstInputs85.lean':'21bc4a16c39fe004912d4122325fffc1291fe55e9c5926281700663c6794e0bb',
 'research/ordinary14-85-main-index-draft/MainIndex85.lean':'7280db4804fd35563116b3b7ad6c9a0f5e60707996279fabd8696e475ec984fe',
 'research/ordinary14-85-direct-norms-draft/DirectNorms85.lean':'2b07f618dc5e76fd6e274596d4425c5c76dbd60919014febb024a9a99265c622',
 'research/ordinary14-85-aux-norm-draft/AuxNorm85.lean':'d2630b6fdd8450042d4c1dff24e119d1fd01b2ed92c23c82097917cefa4716c7',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
}.items():pin(D/path,h)
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)',
 '(hv : ∀ j, 0<v j) (hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'let X := DirectNorms85Draft.X v',
 'have hgap1 : v 1+v 2+1≤q := lt_iff_succ_le.mp hgap',
 'P72FirstInputs85Draft.first_inputs p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'MainIndex85Draft.main_index p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz',
 'DirectNorms85Draft.strong_norm p beta v hport hz',
 'AuxNorm85Draft.aux_norm p beta K MC MF v hport hK hMCcast hMFcast hv hz',
 'P72Exact.indices_ordinary q X Y k R d c a (v 7) (v 4) (v 3) (v 5) (v 11)\n    n s (q^4) m (v 9)',
 'hR26 hny hks hRwindow hnmod hy hnorm hstrong haux',
 'U*d+H*k=U*(X+a*c)+H*(U*v 12+X*Y*q+R+1)',
 'hexact.1,hexact.2.1,hexact.2.2.1,hexact.2.2.2'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-p72-first-inputs-draft-independent','ordinary14-85-main-index-draft-independent',
          'ordinary14-85-direct-norms-draft-independent','ordinary14-85-aux-norm-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
rng=random.Random(85115)
for _ in range(500):
 a,c,f,T,R,u=[rng.randrange(0,20) for _ in range(6)]
 delta=3+4*a+a*a;assert delta==(a+1)*(a+3)
 Vp=f*f*(T*c);Vn=f*f*R+c;Qa=delta*max(f*f-1,0)
 lhs=Qa*abs(Vp-Vn)**2+abs(Vp+u-Vn)**2;rhs=1+Qa*abs(Vp+u-Vn)**2
 assert lhs==delta*max(f*f-1,0)*abs(f*f*(T*c)-(f*f*R+c))**2+abs(f*f*(T*c)+u-(f*f*R+c))**2
 assert rhs==1+delta*max(f*f-1,0)*abs(f*f*(T*c)+u-(f*f*R+c))**2
print(json.dumps({'scope':'source binder and finite shape review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'aux_delta_shapes':500,
 'independent_dependency_reviews':4},sort_keys=True,indent=2))
