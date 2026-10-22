from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
before=(HERE/'reference/KSim.before.lean').read_text()
after=(HERE/'formal/BusyBeaver/ZFC/KSim.lean').read_text()
def declarations(source):
    return {m.group(1):m.group(0).rstrip() for m in
            re.finditer(r'^def (\w+)[\s\S]*?(?=\n\n|\Z)',source,re.M)}
old=declarations(before);new=declarations(after)
assert len(old)==15
checks=[]
for name,body in old.items():
    assert new[name]==body,f'Original definition changed: {name}'
    checks.append({'name':name,'sha256':hashlib.sha256(body.encode()).hexdigest(),'exact_source_unchanged':True})
assert before.splitlines()[:3]==after.splitlines()[:3]
result={'status':'PASS','baseline_commit':'2ca3a5c16f0876d2cab842056353c03a1ed2f5f0',
        'baseline_sha256':hashlib.sha256(before.encode()).hexdigest(),
        'candidate_sha256':hashlib.sha256(after.encode()).hexdigest(),
        'original_definition_count':len(checks),'definitions':checks,
        'imports_exactly_unchanged':True,
        'baseline_lines':len(before.splitlines()),'candidate_lines':len(after.splitlines()),
        'baseline_bytes':len(before.encode()),'candidate_bytes':len(after.encode()),
        'scope':'Exact source comparison for every original def, including 13 executable definitions, Covered and Rel. Public proof API is separately compiler-tested.'}
(HERE/'invariants.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
