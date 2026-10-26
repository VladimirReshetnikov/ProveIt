#!/usr/bin/env python3
"""Verify that isolated coefficient-check data match a supplied ProveIt snapshot."""
from pathlib import Path
import hashlib
import json
import sys

package = Path(__file__).resolve().parent.parent
repo = Path(sys.argv[1]).resolve()
manifest = json.loads((package / 'evidence/arithmetic/extraction_manifest.json').read_text())
fixture = (package / 'lean/candidates/IsolatedCoefficientChecks.lean').read_text()
for item in manifest['extractions']:
    text = (repo / item['source']).read_text()
    if item['declaration'] == 'rowCoefficient':
        start = text.index('def rowCoefficient ')
        end = text.index('\n/--', start)
    elif item['declaration'] == 'envelope':
        start = text.index('def envelope ')
        end = text.index('\ntheorem envelope_lt', start)
    else:
        raise ValueError('Unknown extraction: ' + item['declaration'])
    extracted = text[start:end]
    digest = hashlib.sha256(extracted.encode()).hexdigest()
    if digest != item['sha256'] or extracted not in fixture:
        raise SystemExit('MISMATCH: ' + item['declaration'])
    print('OK:', item['declaration'], digest)
print('Exact extracted data verified; this does not compile the Lean proofs.')
