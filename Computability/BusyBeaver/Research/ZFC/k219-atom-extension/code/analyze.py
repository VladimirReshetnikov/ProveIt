from pathlib import Path
import argparse
import collections
import gzip
import hashlib
import json
import re
import time
import library as lib

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parents[4]
ap = argparse.ArgumentParser(description='Reconstruct all reported roots and full-source DAG counts; no search or runtime.')
ap.add_argument('--work', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
ap.add_argument('--cost', type=int, choices=(4, 5), required=True)
a = ap.parse_args()
P = a.work.resolve()
a.output.mkdir(parents=True, exist_ok=False)
d = P / f'cost{a.cost}'
assert P.is_dir()
execution = json.loads((d / 'execution.json').read_text())
atoms = list(map(lib.frozen, json.loads((P / 'atoms.json').read_text())))
nodes = atoms[:]
root_ids = []
node_text = (d / 'nodes').read_text() if (d / 'nodes').exists() else gzip.decompress((d / 'nodes.gz').read_bytes()).decode()
for line in node_text.splitlines():
    words = line.split()
    if words[0] == 'H':
        left, right, cost = map(int, words[1:])
        assert cost == a.cost and left < len(nodes) and right < len(nodes)
        root_ids.append((nodes[left], nodes[right]))
    else:
        i, left, right, cost = map(int, words)
        assert i == len(nodes) and left < i and right < i and cost < a.cost
        nodes.append((nodes[left], nodes[right]))
intermediate = [int(x) for x in re.findall(r'^HIT (\d+) cost ', (d / 'stdout.log').read_text(), re.M)]
roots = list(dict.fromkeys([nodes[i] for i in intermediate] + root_ids))
tree_path = REPO / 'Computability/BusyBeaver/Research/ZFC/candidate-k219/sites219.json'
old_path = REPO / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-new_equality_macro.json'
tree = lib.parse(json.loads(tree_path.read_text()))
old = lib.frozen(json.loads(old_path.read_text()))
started = time.monotonic()
results = []
for i, macro in enumerate(roots):
    replacement, count = lib.replacement(tree, old, macro)
    assert count == 4
    metrics = lib.metrics(replacement)
    result = {'id': i, 'metrics': metrics, 'macro': macro,
              'macro_leaves': len(lib.leaves(macro)), 'literal_replacements': count}
    # Save literal macros and metrics; full sources are reconstructed on demand.
    if metrics['dag_nodes'] <= 205:
        print(json.dumps({'NEW_SMALL_DAG_DISCOVERY': result}), flush=True)
    results.append(result)
out = {'status': 'LITERAL_REPLACEMENT_DISCOVERY_ANALYSIS', 'seconds': time.monotonic() - started,
       'execution_status': execution['status'], 'root_cost': a.cost, 'stored_nodes': len(nodes),
       'reported_hits': len(intermediate) + len(root_ids), 'unique_macros': len(roots),
       'minimum_full_source_dag': min(r['metrics']['dag_nodes'] for r in results),
       'dag_census': dict(sorted(collections.Counter(r['metrics']['dag_nodes'] for r in results).items())),
       'results': results,
       'scope': 'Finite root0..4 goal plus exact full-source fourfold replacement/DAG count only. Independent wider finite diagnostics and all-natural proof remain separate.'}
(a.output / 'analysis.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: v for k, v in out.items() if k != 'results'}, indent=2))
