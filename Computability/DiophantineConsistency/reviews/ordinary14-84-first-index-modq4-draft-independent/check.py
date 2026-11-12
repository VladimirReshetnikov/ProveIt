#!/usr/bin/env python3
"""Independent first-index congruence source/finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-first-index-modq4-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FirstIndexModQ4.lean','9e773426457e25dbab91ea1b6aee42f1691fc538de000a57cfd7edf3b9f387f2').decode()
pin(A/'check_source.py','a900181c359484d22508f5b2fe6bd8a5d3978b9fd9562e35a79e1332054a9e61')
receipt=pin(A/'observation.json','b13f87c0878c73718d0c18c491bed3a5473100ccf883b69a649d2fd76cd6664f')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-first-index-modq4-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='1013df28e34a4a1e6c97e03926301a0c82c4f2c6d2e188ef267264ebe14e5db8'
for path,h in {
 'ordinary14-84-first-index-residues-draft/FirstIndexResidues.lean':'4963ceffa7f08677b3ecac2bedd11673f3de0426af0883a019fdec01758ac213',
 'ordinary14-84-q4-rank-draft/Q4Rank.lean':'2e57f850c02ce0511c13e9965c7281e8e0f9b63f64c50a9803cc01561969bae6',
}.items():pin(D/'research'/path,h)
pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean','b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c')
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)',
 '(hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'first_index_residues p beta v hbeta (hv 0) (hv 6) (hv 7) hport hz',
 'Q4Rank84Draft.q4_rank p beta K MC MF v hbeta hport hK hMC hMF hv hz',
 'have hm : 0<q^4 := pow_pos hq _',
 'magnitude_mod (R+1,kk) (q^4) hm hmag',
 '⟨4*(X beta v)*q^2*(v 7*v 7)*s,?_⟩',
 'mod_add_remove_left_of_dvd hmultiple hm','hmod\'.symm'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-first-index-residues-draft-independent','ordinary14-84-q4-rank-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=below=above=0
for q in range(1,9):
 for X in range(1,5):
  for yslot in range(1,4):
   Y=q**3*yslot;Q=X*Y*Y;m=q**4
   for n in range(1,5):
    for s in range(3):
     extra=4*Q*s;assert extra==m*(4*X*q*q*yslot*yslot*s)
     k=2*n+extra
     for t in range(-2,3):
      Rplus=k+m*t
      if Rplus<1:continue
      assert abs(Rplus-k)%m==0 and (2*n)%m==Rplus%m
      below+=Rplus<k;above+=Rplus>k;cases+=1
assert below and above
print(json.dumps({'scope':'source and finite congruence controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'congruence_cases':cases,
 'rank_below_k':below,'rank_above_k':above},sort_keys=True,indent=2))
