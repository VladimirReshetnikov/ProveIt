#!/usr/bin/env python3
"""Read-only residual-map source check; not a Lean verification."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent; D=P.parents[1]
pins={'research/adaptive-aq22-quotient110-residual-maps-draft/generate.py': 'a2afdea064f267f5343346ce1930f035208e93365092edf965aa6a22be34e876', 'research/adaptive-aq22-quotient110-residual-maps-draft/AQ22Quotient110ResidualMaps.lean.src': '94d01b77db20c49538ea1b35a3ba2ab638ead80e36d0490ae1d0175071120531', 'research/adaptive-aq22-quotient110-residual-maps-draft/generated.json': '82c533af0d4eef035c15d5b4eae843208555e6a50f6108bb780cbd8e786714e5', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110ConditionalTransfer.lean.src': 'cf38af5ba1e2a24cfbf3d8e5005a3da31b26574e417dfae61ddf4e0cf42a4f31', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Literal.lean.src': 'a763d75e384a7b17ca7deea1a3cbbb08fb87401944e2aa6b4537594465c35219', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110ResidualZeros.lean.src': '7279f9cd51876b4a9764c9ba19c38ca5f9ba2f09df45c5e722318e5c5942d094', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Residuals.lean.src': '569bcc47ad1b0ad31f9b603f0f96afba70496d3feaf221d255cc31f05b41467b', 'research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Witness.lean.src': '501bf108b26cbd5e2d6c84e83a0996b8f3fd9f37949c5f0b2ba6940db3987d2a', 'research/adaptive-aq22-quotient110-model-draft/check.py': 'c3e725c4593e11b87fe1143396ecdb98a9af326c991ea0158a3fced52f885030', 'research/adaptive-aq22-quotient110-model-draft/receipt.json': '908d966815a471c0b8a175a60bc0a4e402f7485b0f707f73fd653a5aa525b3fb', 'research/adaptive-aq22-two-quotients110/check.py': '3fc8a2692cc6c54e81f49a03ece73c4587140fdb442b0ae0b9af7b1f0a2f397d', 'research/adaptive-aq22-two-quotients110/receipt.json': '38dd311675e3d7e19cf339032937129b2f0c317fbc77692e414b92a1908481f2', 'research/adaptive-aq22-two-quotients110/candidate.json': 'b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1', 'Lean/DiophantineConsistency/AdaptiveAQ22Zeros.lean': '68f5256462721aac705c867a3ca7f3d2b39064e85e90d0f72dd7d2198c522f6d'}
for f,h in pins.items(): assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('adaptive-aq22-quotient110-residual-maps-draft','generate.py','generated.json'),('adaptive-aq22-quotient110-model-draft','check.py','receipt.json'),('adaptive-aq22-two-quotients110','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
s=(P/'AQ22Quotient110ResidualMaps.lean.src').read_text()
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
assert sorted(re.findall(r'^theorem relation(\d\d)',s,re.M))==[f'{i:02}' for i in range(13)]
for n in ['extend_project','project_norm0','project_norm1','project_zero','extend_zero','graphZeroObligations','native_equivalence']:
 assert f'theorem {n}' in s,n
for i in range(13): assert s.count(f'rw [relation{i:02d} p v')==1
for i in range(2,13): assert s.count(f'rw [relation{i:02d} p (project v u t)] at hr')==1
print(json.dumps({'scope':'static source and polynomial checker, no Lean','pinned_files':len(pins),'residual_relations':13,'factored_norm_relations':2,'unchanged_residual_relations':11,'extension_cases':13,'projection_cases':13,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
