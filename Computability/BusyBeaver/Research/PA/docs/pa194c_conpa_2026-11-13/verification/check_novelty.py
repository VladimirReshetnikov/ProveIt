#!/usr/bin/env python3
"""Check actual graph novelty against every recognized prior 194-state table.

The exact incremental corpus census has five byte forms in three graph classes,
including the explicitly rejected scanner candidate. Canonicalization forgets
state names and the start, and also tests global left/right reflection.
"""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'comparison'))
from incremental_census import parse, classify

if not __debug__: raise SystemExit('Use Python without -O.')
census = json.loads((ROOT / 'comparison/incremental_census.json').read_text())
assert census['summary']['commit'] == 'b88235336c63a247852fe8ec7f931d51f953632d'
assert census['summary']['top_level_archives'] == 34
forms = [r for r in census['new_raw_tables'] if r['states'] == 194]
assert len(forms) == 5
old = set()
for item in forms:
    path = ROOT / 'comparison/new_frontier_tables' / (item['sha256'] + '.tm')
    content = path.read_bytes()
    assert hashlib.sha256(content).hexdigest() == item['sha256']
    data = parse(content)
    assert data is not None and len(data[1]) == 194
    graph, _ = classify(data)
    assert graph == item['root_free_sha256']
    old.add(graph)
assert len(old) == 3
content = (ROOT / 'tables/pa194C.tm').read_bytes()
data = parse(content)
assert data is not None and len(data[1]) == 194
graph, roots = classify(data)
reflected, _ = classify(data, True)
assert roots == 194 and graph not in old and reflected not in old
assert graph == 'b79f4d344740679b87dace02fe3f211565c2cd4513f346812570d90caa3d9a3f'
print(json.dumps({'status': 'PASS', 'states': 194, 'prior_byte_forms': 5,
                  'prior_root_free_classes': 3, 'full_reaching_roots': roots,
                  'root_free_sha256': graph, 'reflected_root_free_sha256': reflected,
                  'not_a_control_relabeling_or_tape_reflection': True}, indent=2))
