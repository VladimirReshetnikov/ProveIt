#!/usr/bin/env python3
"""Recheck selected source-text claims. This does not compile Lean."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / 'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def headers(text):
    return dict(re.findall(r'^theorem (\w+)\b(.*?):=', text, re.M | re.S))

def main():
    snippets = json.loads((ROOT / 'tactics/findings.json').read_text())['findings']
    for item in snippets:
        text = (SRC / item['file']).read_text()
        require(item['before'] in text, 'Old snippet absent: ' + item['id'])
        require(len(item['before'].splitlines()) == item['before_lines'], 'Old count: ' + item['id'])
        require(len(item['after'].splitlines()) == item['after_lines'], 'New count: ' + item['id'])
    a = (SRC / 'SplitSourceExistence.lean').read_text().splitlines()[97:157]
    b = (SRC / 'GapSourceExistence66.lean').read_text().splitlines()[52:112]
    require(a == b and len(a) == 60, 'Coordinate packaging duplicate changed')
    require(len('\n'.join(a).encode()) == 2292, 'Coordinate duplicate byte count')
    circuits = []
    for family in ('SplitCircuitSteps59', 'GapCircuitSteps66'):
        old = (SRC / (family + '.lean')).read_text()
        new = (ROOT / 'circuits/api_preserving_candidates/DiophantineConsistency' / (family + '.lean')).read_text()
        old_headers, new_headers = headers(old), headers(new)
        require(old_headers == new_headers, 'Public theorem header text differs: ' + family)
        circuits.append({'module': family, 'public_headers': len(old_headers),
                         'old_lines': len(old.splitlines()), 'new_lines': len(new.splitlines()),
                         'old_bytes': len(old.encode()), 'new_bytes': len(new.encode())})
    result = {'status': 'PASS_SOURCE_TEXT_ONLY', 'snippets': len(snippets),
              'coordinate_duplicate_lines': 60, 'coordinate_duplicate_bytes_without_final_newline': 2292,
              'circuits': circuits, 'lean_compilation': 'not performed'}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
