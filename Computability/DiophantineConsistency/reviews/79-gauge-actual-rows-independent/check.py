from pathlib import Path
from hashlib import sha256
import json,re
root=Path('research/ten-positive-79-gauge-actual-rows');o=root/'observations/attempt03'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
r=json.loads((o/'terminal.json').read_text());assert sha(o/'terminal.json')=='c217080816efa02244c270821c54aa1363d70e5068765e276e432471604cd2b1';assert r['status']=='PASS' and r['exit']==0 and r['reason'] is None and sha(root/'run-v3.py')==r['runner_sha256'] and sha(r['output'])==r['output_sha256']=='99cb4d4e542ccef9de028afdd36b2d283c50129c48159a7454198a098cc31151'
for p,v in r['pins'].items():assert sha(p)==v['sha256'] and str(Path(p).resolve())==v['resolved']
for s in ['stdout','stderr']:assert sha(o/s)==r[s+'_sha256']
assert (o/'stdout').read_text().strip()=="'Mask79ActualRows.core_decompose' depends on axioms: [propext]" and not (o/'stderr').read_text()
code=(root/'Mask79ActualRowsV3.lean').read_text();assert re.findall(r'^import\s+(\S+)',code,re.M)==['MaskCoordinate79','Mask79Carrier'];assert 'core p v C G = output (shared p v G) (v 1) C (v 7) := by\n  rfl' in code
shared=code[code.index('def shared'):code.index('\ndef main')];assert set(re.findall(r'\(v (\d+)\)',shared))=={'0','3','4','5','6','8','9'}
assert 'p : Fin 4 → ℤ' in code and 'v : Fin 10 → R' in code and '(C G : R)' in code
for i in (1,2):
 a=root/f'observations/attempt0{i}';t=json.loads((a/'terminal.json').read_text());assert t['status']=='FAILED';assert sha(a/'stdout')==t['stdout_sha256'] and sha(a/'stderr')==t['stderr_sha256']
assert 'error' in (root/'observations/attempt01/stdout').read_text() and 'warning:' in (root/'observations/attempt02/stdout').read_text()
print('PASS: arbitrary-ring core definitional equality, integer ports and free C/G, shared excludes v1/v2/v7, accepted direct pins and retained rejected error/warning attempts checked.')
