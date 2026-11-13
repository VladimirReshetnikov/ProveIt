#!/usr/bin/env python3
"""Source pins and finite rank/parity controls for the toy all-J argument."""
import hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
pins={
 'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
 'research/ordinary14-universal-trace-bound/README.md':'a21b820e49ba6dd71c6c9f7bd933fe1637fbdddbcf86a519a3a4813aaaaf954e',
 'research/ordinary14-shifted-guard87-calibration/README.md':'005fd2c04cef4c997383bf373cc48acd326e829eb01ff4d30c218dadaf9f758a',
 'research/ordinary14-aux-root78/README.md':'461164edefa8b442580c9d186fa1bf1ade7f4d128c9cbc70bbb112f1af52d938',
 'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093',
 'research/ordinary14-direct-x73-q5-toy/result.json':'36c780902131434a1b1e36b8caceb742996249c0ff61726e83a162a0c3c52ee0'}
for name,sha in pins.items():assert hashlib.sha256((D/name).read_bytes()).hexdigest()==sha
beta,K0,MC,MF=4,1,2,5
assert beta>0 and K0>=0 and 0<MC<beta and 0<MF<2*beta
count=0
for J in range(1,21):
    b=beta*J;q=b+1
    assert q>=5 and q%2==1 and math.gcd(q,2)==1
    for F in range(1,q-1):
        for alpha in range(1,q-F):
            G=b*(q-F)+alpha;R=G*(q*q-1)+J*(MC+q*MF)
            assert R>=q**3 and R>=26 and R+q**3+q+1<=q**4
            assert (2*q-1)*(q*q-1)>=q**3
            assert pow(2,R,q)!=0
            count+=1
print(json.dumps({'toy_ports':{'beta':beta,'K0':K0,'MC':MC,'MF':MF},
    'J_values_checked':20,'finite_rank_and_parity_controls':count,
    'scope':'finite controls for a source-dependent all-J toy argument; not a compact44 or Lean result'},sort_keys=True,indent=2))
