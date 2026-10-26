#!/usr/bin/env python3
"""Measure targeted source text only; never compiles Lean."""
from pathlib import Path
import json,re,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'validation'))
from static_audit import mask_noncode
old=(ROOT/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Boundary.lean').read_text()
new=(ROOT/'wang/NorthViewCandidates.lean').read_text()
def declaration(text,name):
    start=re.search(r'^theorem '+re.escape(name)+r'\b',text,re.M)
    if start is None:raise ValueError(name)
    end=re.search(r'^(?:theorem|def|end|#print)\b',text[start.end():],re.M)
    return text[start.start():start.end()+end.start() if end else len(text)]
def count(text):return sum(bool(line.strip()) for line in mask_noncode(text).splitlines())
rows=[]
for name in ['north_435_iff_start','north_434_iff_initLeft','north_436_iff_initializers','north_438_iff_reset','north_437_iff_seam']:
    rows.append({'name':name,'before_nonblank_code_lines':count(declaration(old,name)),
                 'candidate_nonblank_code_lines':count(declaration(new,name+'_candidate'))})
helper=count(new[new.index('def NorthView'):new.index('theorem north_435_iff_start_candidate')])
result={'counts':rows,'shared_helper_nonblank_code_lines':helper,
        'baseline_total':sum(x['before_nonblank_code_lines'] for x in rows),
        'candidate_total_including_helper':sum(x['candidate_nonblank_code_lines'] for x in rows)+helper,'compiled':False}
expected=json.loads((ROOT/'wang/static_metrics.json').read_text())
if result!=expected:raise ValueError('Metric mismatch')
print(json.dumps(result,indent=2))
