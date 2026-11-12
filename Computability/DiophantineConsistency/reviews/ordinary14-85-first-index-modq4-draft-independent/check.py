#!/usr/bin/env python3
"""Independent direct 85 index congruence source/finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-first-index-modq4-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'FirstIndexModQ485.lean','c0374006dcd0a93a991dd7cf3551f902656fdd7750cc92abfcd7abc3cf23b2a7').decode()
pin(A/'check_source.py','dd8f654dfc5dc1ae69bfcd64ee8e2e296708154fe1232907c2b2d0b083763599')
receipt=pin(A/'observation.json','c86fed9011863e80865254c0118a95ea722cd2a3bec0cbfd0a88391d4417946a')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-first-index-modq4-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='fdc8a1a0f2625614edc10989f9d0b25400bbda21da07ff228845ffbebc3ca562'
for path,h in {
 'ordinary14-85-first-index-residues-draft/FirstIndexResidues85.lean':'0f3f24248f51dbac48bcb2b3dcfd0bac2468b1a984fa326a4cd85b0722c6a963',
 'ordinary14-85-q4-rank-draft/Q4Rank85.lean':'40d91f46f65d79aa9c823255f3e92438d5398d8e66ec5c6534da800ac918502f',
}.items():pin(D/'research'/path,h)
pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean','b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c')
for f in ('(hv : ∀ j, 0<v j)','(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'first_index_residues p beta v hbeta (hv 0) (hv 6) (hv 7) hport hz',
 'Q4Rank85Draft.q4_rank p beta K MC MF v hbeta hport hK hMC hMF hv hz',
 'have hm : 0<q^4 := pow_pos hq _','magnitude_mod (R+1,kk) (q^4) hm hmag',
 '⟨4*(X v)*q^2*(v 7*v 7)*s,?_⟩','mod_add_remove_left_of_dvd hmultiple hm',
 "hmod'.symm"):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-first-index-residues-draft-independent','ordinary14-85-q4-rank-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=nondiv=below=above=0
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
      below+=Rplus<k;above+=Rplus>k;nondiv+=X%q!=0;cases+=1
assert below and above and nondiv
print(json.dumps({'scope':'source and finite congruence controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'congruence_cases':cases,
 'rank_below_k':below,'rank_above_k':above,'X_not_divisible_by_q':nondiv},sort_keys=True,indent=2))
