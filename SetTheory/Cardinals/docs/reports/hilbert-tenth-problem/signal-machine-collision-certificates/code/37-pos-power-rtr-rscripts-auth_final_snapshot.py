"""Authenticate revised manuscript/PDF without altering its source tree."""
from pathlib import Path
import json,runpy,shutil
BASE=Path('/workspace/shared/report67-release-independent-review-20261004')
api=runpy.run_path(str(BASE/'auth_snapshot.py'))
inv,sha,enc=api['inventory'],api['sha'],api['encoded']
source=Path('/workspace/shared/report67-power-reductions-release-20261004')
before=inv(source)
expected={'Report67.pdf':'20ef1b64f4a87496bd6c64a72cb760d9d555f4d0d459f84b57cdfd910e1dd800','manuscript/MANUSCRIPT_PINS.json':'99a8beb275e70e66aa4426f1497ccad79a2a4ed13617cce7e6d912ec98a11656','Report67.tex':'fa316a86ba5aa9ddaf15127b52addc3b3f27e85118b1caa1bece85c941caa511','tools/BUILD_DEPENDENCIES_LOCK.json':'924a24fab30a2e05eccd168d7951273e31b99a8adbb3290ab5d8b6f332b884e1','INPUT_PINS.json':'a7061bc1c5b91c4f3940e06530b428f373ad42612c9a31372d7561a4607f8a6a'}
assert all(before['files'][n]['sha256']==h for n,h in expected.items())
old=json.loads((BASE/'CANDIDATE_AUTHENTICATION.json').read_bytes())['inventory']
for n,r in old['files'].items():
    if n.startswith('tools/') or n.startswith('science/') or n.startswith('audits/') or n=='INPUT_PINS.json': assert before['files'][n]==r,n
shutil.copytree(source,BASE/'final-candidate',copy_function=shutil.copy2)
assert before==inv(source)==inv(BASE/'final-candidate')
changed=[n for n,r in before['files'].items() if old['files'].get(n)!=r]
receipt={'status':'PASS','scope':'Updated presentation candidate; not parent final release seal','expected_pins':expected,'source_copy_equal':True,'tools_and_frozen_inputs_unchanged':True,'changed_files':changed,'inventory':before}
(BASE/'FINAL_CANDIDATE_AUTHENTICATION.json').write_bytes(enc(receipt))
print(json.dumps({'status':'PASS','files':len(before['files']),'changed_files':changed}))
