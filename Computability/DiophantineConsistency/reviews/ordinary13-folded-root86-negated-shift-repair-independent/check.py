#!/usr/bin/env python3
"""Review of the restricted scalar-repair criterion; no Lean."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-folded-root86-negated-shift-repair';bt=D/'reviews/ordinary13-folded-root86-negated-positive-bt-independent';forward=D/'reviews/ordinary13-folded-root86-negated-forward-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','84a9b7fbd5030270c3a43114e476354609518e9665dc50d1f9bfc69425e4a1f6'),(P/'check.py','84a2d4b4921c1aa5cab4f2fcdd40cb7a60f71e5ceabe6aff6af40d0f559ff651'),(P/'result.json','1931c92d44fb8011f7bd3f184873271a69728c3f38a9ee1e896dac3041076c45'),(bt/'check.py','676c47df37d52784e45dc39b1a29af36f9cb7caaaaa9beb896fbc96f68f867c8'),(bt/'result.json','6067f43c969e733ca45841f4cb52b9337ef42a35f865b781cac6875abd8bb09a'),(forward/'check.py','a17d6254b2498e2ea3ff6973f290eafb8387d1079d5704a51c063772eb587c83'),(forward/'result.json','f389d54e714a5d51272fcbcb883a7fc27d9bfb7381b380bca313312c177f668e')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-shift-repair-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='a522676d2f1366d8d0e7ae9eb689460dcd464368b0ce751ec525c8dcef666cd9'
for p in (P,bt,forward):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
# Test the arithmetic characterization beyond the author's graph-generated
# finite examples, including cases with D=0 and nontrivial gcd.
count=ok=bad=0
for b in range(1,17):
 q=b+1
 for B in range(2,24):
  A=q*B;L=b//math.gcd(b,B)
  for t in range(-8,1):
   Bt=b*t; d0=L*((1-Bt+A*L-1)//(A*L))
   for cap in range(0,14):
    feasible=[d for d in range(cap+1) if (Bt+A*d)>0 and (Bt+A*d)%b==0]
    assert bool(feasible)==(d0<=cap)
    if feasible:assert min(feasible)==d0;ok+=1
    else:bad+=1
    count+=1
assert ok and bad
print(json.dumps({'status':'PASS_RESTRICTED_CRITERION','independent_arithmetic_controls':count,'feasible_controls':ok,'infeasible_controls':bad,'scope':'criterion only for specified scalar shift and positive-Bt parent repair; no arbitrary reverse existence or Lean'},indent=2))
