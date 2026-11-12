#!/usr/bin/env python3
"""Read-only, bounded source provenance and obligation checker; never runs Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent; D=P.parents[1]
pins = {'research/adaptive-aq26-two-quotients122/candidate.json': '14c9cac4f3af45c15ec5e6df623c83fcab7581ba042aff34c6614dad890154ae', 'research/adaptive-aq26-two-quotients122/natural-candidate.json': '9909fc023d41d060b4edc6a89374f3b88d2f5e83f8b03d45eb5f6f86dc8141ee', 'research/adaptive-aq26-two-quotients122/check.py': 'd83d892b39d2587a1f1a1414a5da10eadc1611b2a2b5495ec43dd0ddeeac2a15', 'research/adaptive-aq26-two-quotients122/receipt.json': 'b153c9751dcae8e6037ee9c4b1b6d3e7df7f992d5be6119c735626619d5f4223', 'Lean/DiophantineConsistency/AdaptiveAQ26Zeros.lean': 'dd49ed0bf68338354dd99498cb091176e21eed281dff0fe252ed8fc99932024c', 'Lean/DiophantineConsistency/AdaptiveAQ26Literal.lean': '91af1d18ff4323623ce77828d08cbfc3d3da92c9fa1bee0e840ae0b74486a441', 'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean': '40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884', 'Lean/DiophantineConsistency/IPRAAQ26Native.lean': '7be42c91618e357ea519fc21afa07fbfd646aa376571d85fd004584b711c37d1', 'research/adaptive-aq26-quotient122-model-draft/AQ26Quotient122ConditionalTransfer.lean.src': 'df0fbd26eb39cd6de845c4438a93a80bb2013afabcfd847008332ae7e0caebec', 'research/adaptive-aq26-quotient122-model-draft/AQ26Quotient122Literal.lean.src': 'a54df6e9150130e72dcdbdfb0e50431a6796323437a99d32b705e7f85afff746', 'research/adaptive-aq26-quotient122-model-draft/AQ26Quotient122ResidualZeros.lean.src': '4536c65020edf06669d53abf8f109e136a19cf3d68ecd6334d752fcf0f5ec3e9', 'research/adaptive-aq26-quotient122-model-draft/AQ26Quotient122Residuals.lean.src': 'b6e1155d0dd45eb4f65f39593168be48acca6cf0825ee24b303f882ff4a1058d', 'research/adaptive-aq26-quotient122-model-draft/AQ26Quotient122Witness.lean.src': '722970a165318f44b878af8b5e477bd9e9b1932aa86cf3340f3f433d3029d1fe', 'research/adaptive-aq26-quotient122-model-draft/generate.py': 'e35ebb215f3023b8d05cc5e18bc85f97776b8f2addd3664be9092db6a9064546', 'research/adaptive-aq26-quotient122-model-draft/generated.json': '673da46b22f6d56b00b5c608f9b4a4283c9bf2ff8fc8bad9c5d5a1bed9a36b3c'}
for name,want in pins.items():
    assert hashlib.sha256((D/name).read_bytes()).hexdigest()==want,name
for packet,check,receipt in [('adaptive-aq26-quotient122-model-draft','generate.py','generated.json'),('adaptive-aq26-two-quotients122','check.py','receipt.json')]:
    path=D/'research'/packet
    out=subprocess.check_output([sys.executable,'-I','-S','-B',str(path/check)],cwd=D)
    assert out == (path/receipt).read_bytes(),packet
texts={f.name:f.read_text() for f in P.glob('*.lean.src')}
assert len(texts)==5
for name,s in texts.items():
    assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),name
w=texts['AQ26Quotient122Witness.lean.src']; c=texts['AQ26Quotient122ConditionalTransfer.lean.src']
assert w.count('ArithmeticAdaptiveQuotients2011.scaled_quotient')==2
for x in ['GraphZeroObligations','hproject','hextend','parent_quotients','IPRAAQ26Native.bridge26','standard_equivalence']:
    assert x in c,x
g=json.loads((D/'research/adaptive-aq26-two-quotients122/candidate.json').read_text())
assert [g['witnesses'][i] for i in (13,14,19,20)]==['scaleVariable','mainScaleVariable','firstQuotient','mainQuotient']
print(json.dumps({'scope':'static source and external checker only; no Lean','pinned_files':len(pins),'source_files':len(texts),'scaled_quotient_uses':2,'graph_zero_obligations_explicit':True,'parent_endpoint':'IPRAAQ26Native.bridge26','source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(texts.items())}},sort_keys=True,indent=2))
