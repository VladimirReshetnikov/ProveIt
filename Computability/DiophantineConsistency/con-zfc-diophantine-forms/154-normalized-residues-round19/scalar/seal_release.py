#!/usr/bin/env python3
"""Seal only the explicit portable mathematical release, excluding all research."""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parent
TOP=['README.md','PROOF.md','SCALAR_FIXED_FRAME_DEGREE_FLOOR.md','BASELINE_PROOF.md','BASELINE_BINDING.json','NOTICE.md','NOTICE_ROUND18_INHERITED.md','build.py','check.py','audit_mutations.py','replay.py','seal_release.py','check_scalar_top_forms.py','circuit.py','five_square_norm.py','exact_polynomial.py','free_whole_center11_c300.json','METRICS.json','SOURCE_PINS.json','CHECK.json','CHECK_OPTIMIZED.json','MUTATIONS.json','MUTATIONS_OPTIMIZED.json','SCALAR_TOP_FORMS_NORMAL.json','SCALAR_TOP_FORMS_OPTIMIZED.json','REPLAY.json']
paths=list(TOP)
for dirname in ['source','coefficients','licenses']:
 for p in (ROOT/dirname).rglob('*'):
  if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':paths.append(p.relative_to(ROOT).as_posix())
paths=sorted(set(paths))
for path in paths:
 if not (ROOT/path).is_file():raise ValueError('missing release path '+path)
whitelist={'schema':'relative-release-whitelist-v1','files':paths+['RELEASE_WHITELIST.json','MANIFEST_SHA256.json'],'scope':'new fixed-frame floor theorem; unchanged attaining degree300/148 graph; all required proof/numeral dependencies; no speculative candidates'}
(ROOT/'RELEASE_WHITELIST.json').write_text(json.dumps(whitelist,indent=2)+'\n')
manifest={}
for name in paths+['RELEASE_WHITELIST.json']:
 raw=(ROOT/name).read_bytes();manifest[name]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
(ROOT/'MANIFEST_SHA256.json').write_text(json.dumps({'schema':'sha256-relative-manifest-v1','files':manifest},indent=2)+'\n')
print(json.dumps({'status':'PASS','release_files':len(whitelist['files']),'manifest_entries':len(manifest),'excluded':['research/','__pycache__/']},indent=2))
