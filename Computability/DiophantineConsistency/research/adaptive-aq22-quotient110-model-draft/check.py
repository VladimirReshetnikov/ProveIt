#!/usr/bin/env python3
"""Read-only, bounded source provenance and obligation checker; never runs Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent; D=P.parents[1]
pins = {'research/adaptive-aq22-two-quotients110/candidate.json': 'b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1', 'research/adaptive-aq22-two-quotients110/natural-candidate.json': '3a86d13d17522c1d662888dbc5149f61023e34c9d04bb7db4c241818ee9ee0a7', 'research/adaptive-aq22-two-quotients110/check.py': '3fc8a2692cc6c54e81f49a03ece73c4587140fdb442b0ae0b9af7b1f0a2f397d', 'research/adaptive-aq22-two-quotients110/receipt.json': '38dd311675e3d7e19cf339032937129b2f0c317fbc77692e414b92a1908481f2', 'Lean/DiophantineConsistency/AdaptiveAQ22Zeros.lean': '68f5256462721aac705c867a3ca7f3d2b39064e85e90d0f72dd7d2198c522f6d', 'Lean/DiophantineConsistency/AdaptiveAQ22Literal.lean': '7d417cd67cc0d6150e3c122e7c4cca4d5c924b54dafe36885f7b5d9b06cf7b6c', 'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean': '40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884', 'Lean/DiophantineConsistency/IPRAAQ22Native.lean': 'b90a9eb67b6fef945e6f1a3c9900e39e3a07a16dbe032089b3489660e00ce747', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110ConditionalTransfer.lean.src': 'cf38af5ba1e2a24cfbf3d8e5005a3da31b26574e417dfae61ddf4e0cf42a4f31', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Literal.lean.src': 'a763d75e384a7b17ca7deea1a3cbbb08fb87401944e2aa6b4537594465c35219', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110ResidualZeros.lean.src': '7279f9cd51876b4a9764c9ba19c38ca5f9ba2f09df45c5e722318e5c5942d094', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Residuals.lean.src': '711df4584209b4dcab07e32c55195ea9d9a82357b71d67b3345f37f447e3d7ca', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Witness.lean.src': '501bf108b26cbd5e2d6c84e83a0996b8f3fd9f37949c5f0b2ba6940db3987d2a', 'research/adaptive-aq22-quotient110-model-draft/generate.py': 'e9f1c3d4a34468f328eb9327cf9ca3861fcf95508e944c6b9533520018c917ca', 'research/adaptive-aq22-quotient110-model-draft/generated.json': '6e283b065d91293deaecc4e57e662625a0bf2f60b80935bacc131be465c6a796'}
for name,want in pins.items():
    assert hashlib.sha256((D/name).read_bytes()).hexdigest()==want,name
for packet,check,receipt in [('adaptive-aq22-quotient110-model-draft','generate.py','generated.json'),('adaptive-aq22-two-quotients110','check.py','receipt.json')]:
    path=D/'research'/packet
    out=subprocess.check_output([sys.executable,'-I','-S','-B',str(path/check)],cwd=D)
    assert out == (path/receipt).read_bytes(),packet
texts={f.name:f.read_text() for f in P.glob('*.lean.src')}
assert len(texts)==5
for name,s in texts.items():
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),name
w=texts['AQ22Quotient110Witness.lean.src']; c=texts['AQ22Quotient110ConditionalTransfer.lean.src']
assert w.count('ArithmeticAdaptiveQuotients2011.scaled_quotient')==2
for x in ['GraphZeroObligations','hproject','hextend','parent_quotients','IPRAAQ22Native.bridge22','standard_equivalence']:
    assert x in c,x
g=json.loads((D/'research/adaptive-aq22-two-quotients110/candidate.json').read_text())
assert [g['witnesses'][i] for i in (13,14,18,19)]==['scaleVariable','mainScaleVariable','firstQuotient','mainQuotient']
print(json.dumps({'scope':'static source and external checker only; no Lean','pinned_files':len(pins),'source_files':len(texts),'scaled_quotient_uses':2,'graph_zero_obligations_explicit':True,'parent_endpoint':'IPRAAQ22Native.bridge22','source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(texts.items())}},sort_keys=True,indent=2))
