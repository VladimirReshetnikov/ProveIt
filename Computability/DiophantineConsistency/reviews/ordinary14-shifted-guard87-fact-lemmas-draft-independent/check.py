#!/usr/bin/env python3
"""Fact-level source signatures and finite arithmetic controls; no Lean."""
import hashlib,json,math,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-shifted-guard87-fact-lemmas-draft';L=D/'Lean/DiophantineConsistency'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
files={P/'README.md':'2d8b0836708c699eb22a34e78f529e52caf573e198bfe72a5f5c935c408f4bef',P/'ShiftedGuardFacts.lean':'1d248d6da88193f3eee50135e12464b7e5765ef51f072bd29a32be6709b78f10',P/'check_source.py':'a3dc52055d95d81e24946007b4f7ec6ee36f92d39732642020c2ea5e04eaf02c',L/'ArithmeticAdaptiveQuotients2011.lean':'40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884',L/'ArithmeticAdaptiveMainOrientation2011.lean':'ad8a0d17ccf06c2f75ce8b095698b66f79869041ae07cf9ff0a376894b4c3968',L/'ArithmeticAdaptiveFactorThree2011.lean':'7679b8e5b0adb93464ca4489c1e24b288718830470764e2c4058c4cd736a64ce',L/'ArithmeticAdaptiveFirstDivisibility2011.lean':'b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c',L/'ArithmeticSignedPairs.lean':'ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d'}
for p,h in files.items():assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent source and mathematical review is recorded in\n`../../reviews/ordinary14-shifted-guard87-fact-lemmas-draft-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='d56c0eeade83478743d9b33618295ac19d92e3d0ced2c3e602c4d4fb83184eca'
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=30);assert not r.stderr and json.loads(r.stdout)['scope']=='source inventory only; no Lean invocation'
s=(P/'ShiftedGuardFacts.lean').read_text();assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for token in ('theorem oriented_scaled_pair','(hscale : 0<scale) (hrad : 0<radicand) (hpos : negative<positive)','theorem sign_free_main_quotient','(hU : 0<U) (hY : 8≤Y) (hk : 0<k) (hrad : 0<radicand)','theorem q4_rank_from_balance','(hq : 0<q) (hY : q^3∣Y)','(hbalance :','q^4∣magnitude (R+1,k)') :assert token in s,token
q=(L/'ArithmeticAdaptiveQuotients2011.lean').read_text();o=(L/'ArithmeticAdaptiveMainOrientation2011.lean').read_text();f=(L/'ArithmeticAdaptiveFactorThree2011.lean').read_text();a=(L/'ArithmeticSignedPairs.lean').read_text()
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m)' in q and 'theorem main_parts_positive (U X Y k eta gamma q R : V)' in o and '(hU : 0<U) (hY : 8≤Y) (hk : 0<k)' in o
assert '(hY : q^3∣Y)' in f and '(hd : q^5∣(3+4*Y*(X+1))*t) : q^4∣t' in f and 'def Equivalent (p q : Pair V)' in a and 'theorem magnitude_of_add' in a
# Independent finite controls of the fact-level numerical implications,
# including q divisible by 3 and non-divisible cases.
count=0
for q in range(1,40):
 for X in range(0,5):
  for s0 in range(0,4):
   Y=q**3*s0;H=3+4*Y*(X+1)
   for t in range(0,30):
    if H*t%(q**5)==0:assert t%(q**4)==0;count+=1
assert count>0
print(json.dumps({'status':'PASS_SOURCE_REVIEW_ONLY','draft_and_sources_pinned':len(files),'finite_factor_three_controls':count,'scope':'uncompiled fact-level proposals with explicit hypotheses; graph, provider and arbitrary-model bridge remain open; no Lean'},indent=2))
