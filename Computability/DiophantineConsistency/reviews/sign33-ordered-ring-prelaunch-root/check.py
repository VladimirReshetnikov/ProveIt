import hashlib
import json
import subprocess
import sys
from pathlib import Path

review = Path(__file__).resolve().parent
root = review.parents[1]
packet = root / 'research/sign33-ordered-ring-standalone-check'
pins = {
    'src/Sign33OrderedRing.lean': '08b041b8f84812f2b9f52f2d6238cdcfa2b977ff2ac1a249776b2c37892927ed',
    'input-pins.json': '2d3cd291b900bd468c4c9cb9ff61cc4bff9d5b2b93e1c95f05a186be51ae2024',
    'run.py': '10b9b1341f032e3f9d9bba501a5d97e6c5641fcdd4eb24bae4525fd8ad32171d',
}
for name, expected in pins.items():
    assert hashlib.sha256((packet / name).read_bytes()).hexdigest() == expected
source = (packet / 'src/Sign33OrderedRing.lean').read_text()
assert all('theorem ' + name in source for name in
           ('gap_tau_signs', 'inner_V_signs', 'auxiliary_difference_sign'))
assert all(hypothesis in source for hypothesis in
           ('F+alpha≤q', '2*r<c', '2≤f', 'S*S*(V*V-y*y)+y*y=1'))
result = subprocess.run([sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight'],
                        capture_output=True, text=True, timeout=90)
assert result.returncode == 0 and not result.stderr
assert json.loads(result.stdout)['status'] == 'PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status': 'PASS_PRELAUNCH_ONLY',
                  'scope': 'Three conditional ordered-ring implications; no Lean or model bridge.'}, sort_keys=True))
