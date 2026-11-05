#!/usr/bin/env python3
"""Read-only source pin check; invokes neither runner nor Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
q=D/'research/p72-p13-p14-translated-fresh';s=D/'research/p72-p13-p14-translated-captured/P72Translated.lean'
pins={'run.py':'cfdd0d172f518ba611dd28a4c5dbbe2b5c495c5f66a4cb0216d7af83ee9b5abc','P72Translated.lean':'324803ca69036a8731c1bb9a65fd635e8a48d29a998c57023eef8f6f1901691a','monitor.py':'d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad'}
for n,h in pins.items():assert sha(q/n)==h
assert sha(s)==pins['P72Translated.lean']
r=(q/'run.py').read_text()
for h in ['ef08b9c68b1f7a770f698b14fc65d221c7db399d924b69c9a3aa9e978464a48a','ca06ffe7d590b250f7585ae75f7aa4a8d9c6e8a12b14096dc56ec55caeed41aa','f4bbe5f0b543497d543f243e10d8ead6d778cc3d0bf0aec96dfa73f7e622dd5a','a0cad18c8a85f74f1d69f57b7c510fa56a488726c66cbfc96421f88476acfa07']:assert h in r
print(json.dumps({'status':'PASS_SOURCE_PIN_REVIEW_ONLY','pins':pins,'scope':'No preflight, Lean launch, provider audit rerun, or compile result.'},indent=2,sort_keys=True))
