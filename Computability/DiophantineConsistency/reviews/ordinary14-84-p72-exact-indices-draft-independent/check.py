#!/usr/bin/env python3
"""Independent P72 binder/source review; no Lean invocation."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-p72-exact-indices-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'P72ExactIndices.lean','504541280d0258606602d9d22af9c6573b8749dfdbc0dd243d77618e6f919640').decode()
pin(A/'check_source.py','d005d5e3d83c5932238d3962627e164df7bd965a9c01f6d7e371f8c41c4222c0')
receipt=pin(A/'observation.json','dd4374ced5dca27487c77a8aec0fec94649d115f3decbbe48442e907370c00ec')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-p72-exact-indices-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='eeef47da825c183e9359a38d2ec405e2aba628f2a0364440a1e62d0e3f38223b'
for path,h in {
 'research/ordinary14-84-p72-first-inputs-draft/P72FirstInputs.lean':'66f7552cbc7b89a42e1bd81366313bd1d4ee77aafec29368623fc210b864cab8',
 'research/ordinary14-84-main-index-draft/MainIndex.lean':'fb9fa47c9d358e5bfe0fbd22f843172bd6df47d71ada1584e20ec68aa4147e75',
 'research/ordinary14-84-strong-norm-draft/StrongNorm.lean':'18097a1230b0f935bda91a82b5ad314a64b05f9e6b07c3436f18e5cc95aa7a0d',
 'research/ordinary14-84-aux-norm-draft/AuxNorm.lean':'42f422ac8b96eac7d4d1b8fe6e10bd6c9ec7d3c4a98f6d6f22eeddba9e511ddc',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
}.items():pin(D/path,h)
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)',
 '(hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'have hgap1 : v 1+v 2+1≤q := lt_iff_succ_le.mp hgap',
 'P72FirstInputs84Draft.first_inputs p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'MainIndex84Draft.main_index p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz',
 'StrongNorm84Draft.strong_norm p beta v hport hz',
 'AuxNorm84Draft.aux_norm p beta K MC MF v hport hK hMCcast hMFcast hv hz',
 'P72Exact.indices_ordinary q X Y k R d c a (v 7) (v 4) (v 3) (v 5) (v 11)\n    n s (q^4) m (v 9)',
 'hR26 hny hks hRwindow hnmod hy hnorm hstrong haux',
 'hexact.1,hexact.2.1,hexact.2.2.1,hexact.2.2.2',
 'hny,hks,hx,hy,hbal'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-p72-first-inputs-draft-independent','ordinary14-84-main-index-draft-independent',
          'ordinary14-84-strong-norm-draft-independent','ordinary14-84-aux-norm-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
rng=random.Random(84115);cases=0
for _ in range(500):
 a,c,f,T,R,u=[rng.randrange(0,20) for _ in range(6)]
 delta=3+4*a+a*a;assert delta==(a+1)*(a+3)
 Vp=f*f*(T*c);Vn=f*f*R+c;Qa=delta*max(f*f-1,0)
 lhs=Qa*abs(Vp-Vn)**2+abs(Vp+u-Vn)**2
 rhs=1+Qa*abs(Vp+u-Vn)**2
 # The P72 haux binder uses precisely these natural grouped expressions.
 assert lhs==delta*max(f*f-1,0)*abs(f*f*(T*c)-(f*f*R+c))**2+abs(f*f*(T*c)+u-(f*f*R+c))**2
 assert rhs==1+delta*max(f*f-1,0)*abs(f*f*(T*c)+u-(f*f*R+c))**2
 cases+=1
print(json.dumps({'scope':'source binder and finite shape review only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'aux_delta_shapes':cases,
 'independent_dependency_reviews':4},sort_keys=True,indent=2))
