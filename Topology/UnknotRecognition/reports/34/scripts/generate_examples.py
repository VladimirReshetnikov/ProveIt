"""Recompute the source-bound kernel certificate for each supplied example."""
import json
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from braidkernel import Braid, kernelize
for path in sorted((ROOT/'examples').glob('*.json')):
    if path.stem.endswith('_certificate'):
        continue
    source = json.loads(path.read_text())
    answer = kernelize(Braid.checked(source['strands'], source['word']))
    path.with_name(path.stem+'_certificate.json').write_text(json.dumps(answer, indent=2)+'\n')
    print(path.name, answer['status'], answer['stats']['core_letters'])
