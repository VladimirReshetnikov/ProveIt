#!/usr/bin/env python3
"""Reproduce a sign33 specialization of the checked sign38 macro language; not a Lean proof."""
import hashlib,json,sys
from pathlib import Path
P=Path(__file__).resolve().parent
src=P.parent/'nine-seed38-jones-compact-language-retry01/src/DiophantineConsistency/Norm38MacroLanguage.lean'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if H(src)!='8b25a5ac8047503064f7d044c0d17f36f39b458902b8e927c8ec685fc8677b3f':raise RuntimeError('source pin')
s=src.read_text()
for old,new in [('Norm38NamedFormula','Sign33NamedFormula'),('Norm38MacroLanguage','Sign33MacroLanguage'),('SharingSeed38','SharingSeed33'),('Fin 39','Fin 34'),('Fin 40','Fin 35'),('codingExpo 38 4','codingExpo 33 4'),('codingStar 38 4','codingStar 33 4')]:
 if old not in s:raise RuntimeError('missing '+old)
 s=s.replace(old,new)
if '38' in s or 'Fin 40' in s:raise RuntimeError('unreplaced specialization')
out=P/'Sign33MacroLanguage.lean'
if sys.argv[1:]==['--check']:
 if out.read_text()!=s:raise RuntimeError('generated language mismatch')
 print(json.dumps({'status':'PASS_SOURCE_REGENERATION_ONLY','source_sha256':H(src),'output_sha256':H(out),'scope':'No Lean parse or semantic theorem.'},sort_keys=True))
else:raise SystemExit('expected --check')
