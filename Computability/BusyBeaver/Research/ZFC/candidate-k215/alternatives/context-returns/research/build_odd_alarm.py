#!/usr/bin/env python3
"""Reproduce the uncalibrated parity/disequality source experiment."""
from pathlib import Path
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'machine'
spec = importlib.util.spec_from_file_location('source_language', HERE.parent / 'code/source_language.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)

raw = (BASE / 'sites215.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
p = s.tree(json.loads(raw))
rows = s.sites(p)
implication = s.subtree(p, '1101001001010')
negation = s.subtree(p, '11010010011101010110001111011')
assert len(s.sites(implication)) == 27
assert len(s.sites(negation)) == 47
assert s.boundary(implication) == s.boundary(negation) == (0, 0, False)
word = [row[1:] for row in s.sites(implication)]
paths = []
for i in range(len(rows) - 30):
    if [r[1:] for r in rows[i:i+27]] == word and all(r[1:] == ['CI', 1] for r in rows[i+27:i+30]):
        assert rows[i+30][1:] != ['CI', 1]
        paths.append(rows[i+29][0])
assert len(paths) == 6
q = p
for path in paths:
    q = s.replace(q, path, (('CI', 1), negation))
scanner = (('CD', 5), ((('CD', 5), ('CC', 2)), ('CH', None)))
assert s.boundary(scanner) == (0, 0, True)
q = s.replace(q, '111', (scanner, s.subtree(p, '11111')))
encoded_rows = s.sites(q)
assert s.graph_intervals(encoded_rows) == s.graph_arithmetic(encoded_rows)[0]
output = s.compact(encoded_rows)
(HERE / 'sites-oddalarm-diseq.json').write_bytes(output)
receipt = {
    'status': 'SOURCE_EXPERIMENT_REVERSE_CALIBRATION_OPEN',
    'sha256': hashlib.sha256(output).hexdigest(),
    'metrics': s.metrics(q),
    'tag3_constructor_endings': paths,
    'two_CFG_resolvers_agree': True,
    'scanner': 'halt iff H is odd; otherwise clear H and return',
    'open_obligation': 'Support-aware formula encoder, logical embedding, and encodable-bundle/ZFC comparison for negative equality; no binary allocation.',
}
(HERE / 'odd_alarm_results.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
