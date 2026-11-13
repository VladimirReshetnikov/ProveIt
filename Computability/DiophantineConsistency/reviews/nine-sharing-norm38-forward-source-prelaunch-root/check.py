import hashlib
import json
import subprocess
import sys
from pathlib import Path

review = Path(__file__).resolve().parent
root = review.parents[1]
packet = root / 'research/nine-sharing-norm38-forward-source-check'
pins = {
    'source-manifest.json': 'bec8903d2b084d38ba31648de663267d2e12b1f471c64a9601e694011119ee55',
    'provider_survey.py': 'c939eae7448754104ca9f9d8d978b08845374381a879bf830327e33922e486a6',
    'run.py': '3a1194b5cbb8378f3a7e13829df9b89ed0ab5a4138c29998f0fa8cc31199b35a',
}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for name, expected in pins.items():
    assert sha(packet / name) == expected
manifest = json.loads((packet / 'source-manifest.json').read_text())
assert [r['module'].split('.')[-1] for r in manifest['rows']] == [
    'Norm38ForwardFiveNorms', 'Norm38SourceToSeed']
for row in manifest['rows']:
    source = packet / 'src/DiophantineConsistency' / (row['module'].split('.')[-1] + '.lean')
    assert sha(source) == row['source_sha256']
reviewed = root / 'reviews/nine-sharing-norm38-forward-five-norms-draft-independent/check.py'
for command in ([sys.executable, '-I', '-S', '-B', str(reviewed)],
                [sys.executable, '-I', '-S', '-B', str(packet / 'run.py'), '--preflight']):
    result = subprocess.run(command, capture_output=True, text=True, timeout=90)
    assert result.returncode == 0 and not result.stderr
print(json.dumps({'status': 'PASS_PRELAUNCH_ONLY',
                  'scope': 'Source and point-provider review; no Lean run or endpoint.'}, sort_keys=True))
