"""Run the self-contained verification suite and refresh evidence receipts."""
import json
from pathlib import Path
import shutil

import verify

ROOT = Path(__file__).resolve().parent


def main():
    verify.main()
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    shutil.copyfile(ROOT / 'verification.json', evidence / 'verification.json')
    report = json.loads((ROOT / 'verification.json').read_text())
    (evidence / 'metrics.json').write_text(json.dumps({
        'python': report['python'], 'programs': report['metrics']}, indent=2) + '\n')
    shutil.copyfile(ROOT / 'provenance.json', evidence / 'provenance.json')


if __name__ == '__main__':
    main()
