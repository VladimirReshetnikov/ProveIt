#!/usr/bin/env python3
"""Read-only source coverage and external algebra check; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/adaptive-aq20-substituted104-residual-maps-draft/generate.py': 'f8ba781cc59c0dcddb8d7207da49fed2bc7c9190766ec4e6e92f12f7c00660ff', 'research/adaptive-aq20-substituted104-residual-maps-draft/AQ20Substituted104ResidualMaps.lean.src': 'dc8c23f1532b141b3842c20bf3a19a03bce60c7cf62b45935cba26931ed4dd1d', 'research/adaptive-aq20-substituted104-residual-maps-draft/generated.json': '72a15b88d4cb6e180baa4e89deed95fabd06ea047eda617b9aed79e8bb9cba6b', 'research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104ConditionalTransfer.lean.src': 'a4e44c67ead30d3a9503a01b31d021dc63b182d2af648cbbc80670809f21d93e', 'research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104Literal.lean.src': '4f37e98904b491e3c5d04265917902be23d4b661c28153e890b6e9712f796e4c', 'research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104ResidualZeros.lean.src': 'ae0f321216013671a767a2e2c44cf1bbe89ddc0c8f6a67a61345afc8a92ca348', 'research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104Residuals.lean.src': '15d6509b3bc49521b1b1e11b7090c9a30d43643116d471e6b596a4f5304acf4d', 'research/adaptive-aq20-substituted104-model-draft/check.py': '3dea1f0b922858e11db0d08b3bcac8c86717be8a1ecb60e5ad575addb157528a', 'research/adaptive-aq20-substituted104-model-draft/receipt.json': '625a49c9713d41ef90e21996f4e661768b01db1365f2e0457329b47499ff06e8', 'research/adaptive-aq20-substituted-scales104/check.py': '93142731c1746adc068682d92094822fdecdd662a56ac9adc76fbe9662bd60ed', 'research/adaptive-aq20-substituted-scales104/receipt.json': '792bd8e4a41b11c025d5cc8ed29a22608caed337c212414a305f64eca1423eb6', 'research/adaptive-aq20-substituted-scales104/candidate.json': 'e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50', 'Lean/DiophantineConsistency/AdaptiveAQ22Zeros.lean': '68f5256462721aac705c867a3ca7f3d2b39064e85e90d0f72dd7d2198c522f6d'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('adaptive-aq20-substituted104-residual-maps-draft','generate.py','generated.json'),('adaptive-aq20-substituted104-model-draft','check.py','receipt.json'),('adaptive-aq20-substituted-scales104','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
s=(P/'AQ20Substituted104ResidualMaps.lean.src').read_text()
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
assert sorted(re.findall(r'^theorem relation(\d\d)',s,re.M))==[f'{i:02}' for i in range(11)]
for n in ['binding04','binding05','parent_scales','extend_project','project_zero','extend_zero','graphZeroObligations']:
 assert f'theorem {n}' in s,n
for i in range(11):
 assert s.count(f'rw [relation{i:02d} p beta v hb]')==1
 assert s.count(f'rw [relation{i:02d} p beta (project v) hb] at hr')==1
print(json.dumps({'scope':'static source and external polynomial checker, no Lean','pinned_files':len(pins),'equal_residuals':11,'vanishing_bindings':2,'extension_cases':13,'projection_cases':11,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
