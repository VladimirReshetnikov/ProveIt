from pathlib import Path
from hashlib import sha256
import json,re
base=Path('/tmp/p65-canonical-endpoint-provider'); manifest=json.loads((base/'manifest.json').read_text())
if manifest['missing']:raise SystemExit(f'unresolved: {manifest["missing"]}')
for entry in manifest['order']:
 orig=Path(entry['original']).read_bytes();shim=Path(entry['shim']).read_bytes()
 if sha256(orig).hexdigest()!=entry['source_sha256'] or sha256(shim).hexdigest()!=entry['shim_sha256']:
  raise SystemExit('source hash mismatch: '+entry['module'])
 expected=re.sub(r'^(import\s+)(\S+)',lambda m:m.group(1)+entry['imports'][m.group(2)],orig.decode(),flags=re.M).encode()
 if expected!=shim:raise SystemExit('non-import source change: '+entry['module'])
for k,entry in manifest['bindings'].items():
 obj=Path(entry['object'])
 if not obj.is_file() or sha256(obj.read_bytes()).hexdigest()!=entry['sha256']:
  raise SystemExit('provider object mismatch: '+k)
shimobj=Path('/tmp/P65GraphShim.olean')
if sha256(shimobj.read_bytes()).hexdigest()!='7bd2902eeffa586418aedef1aded667be68d32c0aeb6f3946a09d277db3dc19c':
 raise SystemExit('P65GraphShim object mismatch')
print('checked',len(manifest['order']),'source shims,',len(manifest['bindings']),'captured object bindings, and P65GraphShim')
