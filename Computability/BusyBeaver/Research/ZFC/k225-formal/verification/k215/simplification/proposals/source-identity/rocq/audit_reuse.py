#!/usr/bin/env python3
"""Static source/size audit only. Never imports or runs downloaded source."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
S = ROOT / 'sources'

def git_blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

sources = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text())
for item in sources:
    data = (S / item['file']).read_bytes()
    assert len(data) == item['bytes'], item['file']
    assert git_blob(data) == item['blob_sha1'], item['file']

p = (S / 'ProgLibPerm.v').read_text()
q = (S / 'ProgLib219.v').read_text()
body_start = '(** ** Determinism'
pb = p[p.index(body_start):]
qb = q[q.index(body_start):].replace('dag219', 'dagPerm')
assert pb == qb

old = re.search(r'Lemma z465 a :.*?Qed\.', p, re.S).group()
new = '''Lemma z465 a : forall m, get m 5 = a -> sem (ENode 465) m XNormal (set m 5 0).
Proof.
  intros m _. revert m.
  while_tac (fun m : St => m) (fun m : St => set m 5 0).
Qed.'''
gen = (S / 'regenerate218.py').read_text()
assert old in gen, 'The maintained producer must own the exact old proof.'
assert old in q, 'The 218 generated library must have the same proof.'
dag = (S / 'DagPerm.v').read_text()

def row(text, n):
    return re.search(r'\| ' + str(n) + r' => (.*)', text).group(1)

assert row(dag, 199) == row(dag, 465) == '(EDecnz 5, EContinue 1)'
wrong_dag = dag.replace('| 465 => (EDecnz 5, EContinue 1)',
                        '| 465 => (EDecnz 5, EContinue 2)')
assert row(wrong_dag, 465) != row(dag, 199)
assert 'while_tac (fun m : St => m) (fun m : St => set m 5 0)' in p

out = {
    'pin': 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6',
    'method': 'Static byte, string, and literal-row checks only; no Rocq check.',
    'verified_source_files': len(sources),
    'macro_duplicate_body': {
        'start': body_start, 'lines': len(pb.splitlines()),
        'bytes': len(pb.encode()), 'identifier_normalization': 'dag219 -> dagPerm',
        'equal': True},
    'z465': {
        'old_lines': len(old.splitlines()), 'old_bytes': len(old.encode()),
        'proposed_lines': len(new.splitlines()), 'proposed_bytes': len(new.encode()),
        'line_reduction_per_copy': len(old.splitlines()) - len(new.splitlines()),
        'byte_reduction_per_copy': len(old.encode()) - len(new.encode()),
        'producer_contains_identical_old_proof': True,
        'same_statement': old.split('\n')[0] == new.split('\n')[0],
        'same_graph_row_as_w199': True,
        'negative_control_wrong_continue_level_rejected': True,
        'compiled': False},
    'upstream_sources_executed': False,
    'repository_changes': False,
}
(ROOT / 'REUSE_AUDIT.json').write_text(json.dumps(out, indent=2) + '\n')

# Emit a suggested producer-only diff; generated outputs must be refreshed by
# the repository's authorized producer/build workflow before adoption.
import difflib
path = 'Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/regenerate218.py'
patch = ''.join(difflib.unified_diff(gen.splitlines(True), gen.replace(old, new).splitlines(True),
                                  fromfile='a/' + path, tofile='b/' + path))
(ROOT / 'z465_producer.proposal.patch').write_text(patch)
print(json.dumps(out, indent=2))
