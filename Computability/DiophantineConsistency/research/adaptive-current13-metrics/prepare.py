"""One-time data-only preparation. No project code or compiler is invoked."""
from pathlib import Path
import copy
import hashlib
import json
import shutil

HERE = Path(__file__).resolve().parent
D = HERE.parents[1]


def record(path):
    raw = path.read_bytes()
    return {'path':str(path.relative_to(D)), 'bytes':len(raw),
            'sha256':hashlib.sha256(raw).hexdigest()}


def put(name, value):
    target = HERE/name
    if target.exists():
        raise RuntimeError('Refusing to replace prepared data: '+name)
    target.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')


files = [
    'Lean/DiophantineConsistency/NativeAdaptiveGraph.lean',
    'Lean/DiophantineConsistency/NativeAdaptiveGraphChecks.lean',
    'Lean/DiophantineConsistency/NativeAdaptiveCurrent2011.lean',
    'Lean/DiophantineConsistency/NativeAdaptiveCurrent2011Checks.lean',
    'Lean/DiophantineConsistency/DecimalMachine215.lean',
    'Lean/DiophantineConsistency/WangTiles942Data.lean',
    'Lean/DiophantineConsistency/WangTiles942TableData.lean',
    'Lean/DiophantineConsistency/WangTiles942PhysicalData.lean',
    'Lean/DiophantineConsistency/CurrentMaskData2011.lean',
    'Lean/DiophantineConsistency/CurrentKernelData2011.lean',
    'candidates/free-j-polarized-positive/source/positive/p13_free_J.json',
    'research/native-adaptive-graph-binding/BINDING.json',
    'research/padding-staircase-independent/coefficients.json',
    'research/padding-staircase-independent/certificate.json',
    'research/padding-staircase-independent/PROOF.md',
    'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json',
    'reviews/native-adaptive-graph-root.md',
    'reviews/native-adaptive-current2011-root.md',
    'reviews/native-adaptive-current2011-peer.md',
    'reviews/native-adaptive-current2011-peer-replay.json',
    'reviews/native-adaptive-current2011-root-auth/ROOT.json',
    'research/adaptive-current13-metric-plan-20261027.md',
]
parent_path = D/files[10]
parent = json.loads(parent_path.read_text())
page_path = D/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json'
page = json.loads(page_path.read_text())
binding = copy.deepcopy(page['coefficient_binding'])
for entry in binding['ports'].values():
    files.append(str((page_path.parent/'coefficients'/entry['file']).relative_to(D)))
put('INPUTS.json', {'scope':'Immutable pre-audit source/data/accepted-equivalence pins; no new Lean build',
                   'files':[record(D/name) for name in files]})
graph = {
    'schema':'literal_integer_arithmetic_dag_v1',
    'name':'current2011_adaptive13_88_degree51',
    'domain':'strictly positive integers',
    'witnesses':parent['witnesses'], 'fixed_numerals':parent['fixed_numerals'],
    'source':parent['source'], 'output':parent['output'],
    'operations':88, 'operation_breakdown':{'*':48,'+':23,'-':17},
    'exact_degree':51, 'coefficient_binding':binding,
    'literal_parent':str(parent_path.relative_to(D)),
    'literal_parent_sha256':record(parent_path)['sha256'],
    'lean_graph':'../../Lean/DiophantineConsistency/NativeAdaptiveGraph.lean',
    'lean_current':'../../Lean/DiophantineConsistency/NativeAdaptiveCurrent2011.lean',
    'metric_proof':'PROOF.md',
    'scope':'Finite exact schedule/degree/full current ports; existing external Lean positive-zero equivalence, no internal HA/PA/ZFC claim or global minimum',
}
put('polynomial.json', graph)
for entry in binding['ports'].values():
    target = HERE/'coefficients'/entry['file']
    target.parent.mkdir(exist_ok=True)
    if target.exists():
        raise RuntimeError('Refusing to replace coefficient')
    shutil.copyfile(page_path.parent/'coefficients'/entry['file'], target)
print(json.dumps({'status':'PREPARED', 'input_manifest':record(HERE/'INPUTS.json'),
                  'graph':record(HERE/'polynomial.json'), 'pinned_files':len(files)}, indent=2))
