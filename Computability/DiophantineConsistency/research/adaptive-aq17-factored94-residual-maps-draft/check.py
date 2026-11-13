#!/usr/bin/env python3
"""Read-only source coverage and external algebra checks; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/adaptive-aq17-factored94-residual-maps-draft/generate.py': 'f779f921110ec31486529a0eab7fb154730a0a29bc0a26f4847dd95ef59a82ea', 'research/adaptive-aq17-factored94-residual-maps-draft/AQ17Factored94ResidualMaps.lean.src': '031ce00dabc454bda89a8b8a5154f148addc2b7dce127559e467cc710a205584', 'research/adaptive-aq17-factored94-residual-maps-draft/generated.json': '0de972fe1c070a516d477f16bc2e69aa2ef1b83f3f3ff4f360074a258bc8fd96', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94ConditionalTransfer.lean.src': '37d82d6ffc27958025a2752f2c7171b66b8318a801cd314dab74c2a279458d66', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94Literal.lean.src': 'd419db2a442456bb31c135b3270ab3c19916e04c79f996d02727b36f399333e7', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94ResidualZeros.lean.src': '21ee415b10988e4cc9dac54e21b15c72a53de0e53caec7d46db032567403036c', 'research/adaptive-aq17-factored94-model-draft/AQ17Factored94Residuals.lean.src': '317e919190e12bafd6bd641338ed154bb2ee201fc3f1c8fe71f9ed645d9418e3', 'research/adaptive-aq17-factored94-model-draft/check.py': 'a0dbc08e46f7212ff59ecaee8768b61fbe7bde6a86e559645d425e328dace58f', 'research/adaptive-aq17-factored94-model-draft/receipt.json': 'a21c9d545217d4f3a84a60aebb0bb0b81e1e567e13b35be9b2e18802dfd8e559', 'research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104Residuals.lean.src': '15d6509b3bc49521b1b1e11b7090c9a30d43643116d471e6b596a4f5304acf4d'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('adaptive-aq17-factored94-residual-maps-draft','generate.py','generated.json'),('adaptive-aq17-factored94-model-draft','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
s=(P/'AQ17Factored94ResidualMaps.lean.src').read_text()
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
assert sorted(re.findall(r'^theorem relation(\d\d)',s,re.M))==[f'{i:02}' for i in range(8)]
for n in ['binding05','binding06','binding10','parent_bindings','extend_project','project_zero','extend_zero','graphZeroObligations']:
 assert f'theorem {n}' in s,n
for i in range(8):
 assert s.count(f'rw [relation{i:02d} p v]')==1
 assert s.count(f'rw [relation{i:02d} p (project v)] at hr')==1
print(json.dumps({'scope':'static source and external graph checks, no Lean','pinned_files':len(pins),'equal_residuals':8,'vanishing_bindings':3,'extension_cases':11,'projection_cases':8,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
