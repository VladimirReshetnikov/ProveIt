"""Remeasure incumbent source files without executing their checkers."""
import json
import platform
from pathlib import Path
from verify import measure

ROOT = Path(__file__).resolve().parents[1]

def main():
    provenance = json.loads((ROOT / 'reference/checkers/PROVENANCE.json').read_text())
    rows = []
    for source in provenance['sources']:
        metrics = measure(ROOT / source['file'])
        if metrics['source_sha256'] != source['source_sha256']:
            raise RuntimeError('Changed incumbent source: ' + source['file'])
        rows.append({**metrics, 'contract': source['contract']})
    result = {'python': platform.python_version(),
              'snapshot': provenance['snapshot'],
              'note': 'Each row is one full program. Different contracts must remain separate.',
              'programs': rows}
    (ROOT / 'evidence/frontier_metrics.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()

