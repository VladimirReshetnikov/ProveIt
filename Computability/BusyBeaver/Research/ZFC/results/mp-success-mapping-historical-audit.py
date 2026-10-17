"""Independent finite artifact/segment-certificate audit; no machine search/build."""
from pathlib import Path
from collections import Counter
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
RESEARCH = ROOT / 'Computability/BusyBeaver/Research/ZFC'
WORK = Path('/tmp/zfc-mp-literal-map')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

bi = load('child_bisim_parser', RESEARCH / 'bisim254.py')
au = load('child_candidate_parser', RESEARCH / 'candidate252_independent_audit.py')
p = json.loads((WORK / 'modified-Prog254-rows.json').read_text())
d = json.loads((WORK / 'modified-Dag254-rows.json').read_text())
cert = json.loads((WORK / 'modified-segment-certificate.json').read_text())
basep = json.loads(json.dumps(bi.load_prog254()))
based = json.loads(json.dumps(bi.load_dag254()))
pdiff = [(i, b, basep[i][b], p[i][b]) for i in range(len(p)) for b in (0, 1) if p[i][b] != basep[i][b]]
ddiff = [(i, b, based[i][b], d[i][b]) for i in range(len(d)) for b in (0, 1) if d[i][b] != based[i][b]]
assert pdiff == [(6423, 1, ['node', 6434], ['node', 6453])], pdiff
assert ddiff == [(130, 1, ['node', 166], ['node', 167])], ddiff

# These functions are deliberately separate from bi.Prog/seg/build. They model
# actual RegisterPath walk consumption, carry zeros, and break/continue stripping.
def walk(rows, pointer):
    node = 0
    consumed = []
    for depth in range(len(rows) + 1):
        bit = pointer[depth] if depth < len(pointer) else False
        consumed.append(bit)
        kind, arg = rows[node][int(bit)]
        if kind != 'node':
            return kind, arg, consumed
        node = arg
    raise AssertionError('finite walk exhausted')

def inc(pointer):
    result = list(pointer)
    for i in range(len(result) - 1, -1, -1):
        if result[i]:
            result[i] = False
        else:
            result[i] = True
            break
    return result

def pop(pointer, bit, count):
    result = list(pointer)
    while result and count:
        x = result.pop()
        if x == bit:
            count -= 1
    return result

def segment(rows, pointer):
    increments = Counter()
    for length in range(1000):
        kind, arg, consumed = walk(rows, pointer)
        if kind in ('decnz', 'halt'):
            return increments, list(pointer), length
        if kind == 'inc':
            increments[arg] += 1
            pointer = inc(consumed)
        elif kind == 'brk':
            pointer = inc(pop(consumed, False, arg))
        elif kind == 'cont':
            pointer = pop(consumed, True, arg)
        else:
            raise AssertionError(kind)
    raise AssertionError('finite segment exhausted')

def check_segment(a, b, target):
    ca, pa, la = segment(p, a)
    cb, pb, lb = segment(d, b)
    assert ca == cb
    assert 0 <= target < len(cert)
    assert (pa, pb) == (cert[target][0], cert[target][1])
    return max(la, lb)

max_segment = check_segment([], [], 0)
assert cert[0][0] == cert[0][1] == []
halt_pairs = 0
edges = 0
graph = {}
for i, (a, b, nz, zero) in enumerate(cert):
    ka, ra, qa = walk(p, a)
    kb, rb, qb = walk(d, b)
    assert ka == kb
    if ka == 'halt':
        assert nz == zero == 0
        halt_pairs += 1
        graph[i] = []
        continue
    assert ka == 'decnz' and ra == rb
    max_segment = max(max_segment, check_segment(inc(qa), inc(qb), nz))
    max_segment = max(max_segment, check_segment(inc(pop(qa, False, 1)), inc(pop(qb, False, 1)), zero))
    edges += 2
    graph[i] = [nz, zero]
seen = set()
todo = [0]
while todo:
    i = todo.pop()
    if i in seen:
        continue
    seen.add(i)
    todo.extend(graph[i])
assert len(seen) == len(cert)
assert len({(tuple(row[0]), tuple(row[1])) for row in cert}) == len(cert)

def leaves(rows, node=0, prefix=()):
    result = []
    for bit, (kind, arg) in enumerate(rows[node]):
        path = prefix + (bit,)
        if kind == 'node':
            result.extend(leaves(rows, arg, path))
        else:
            result.append((path, kind, arg))
    return result

sites = leaves(p)
guards = sum(2 if op == 'decnz' else 1 for _, op, _ in sites)
assert (len(sites), guards) == (6441, 8366)
table_path = RESEARCH / 'candidate-permutation252/zfc_permutation252_old.tm'
table = au.read_table(table_path.read_bytes())
assert sha(table_path) == au.EXPECTED_SHA
assert len(table) == 504 and len({q for q, _ in table}) == 252
assert table[204, 1] == (1, 'R', 113)
assert table[113, 1] == (1, 'R', 132)
changed = dict(table)
changed[204, 1] = (1, 'R', 132)
assert len(au.BOX_PAIRS) == 55
assert all(changed[k] == table[k] for k in au.BOX_PAIRS)
chain = []
q = 96
for i in range(6):
    action = changed[q, 1]
    assert action[:2] == (1, 'R')
    chain.append([q, 1, *action])
    q = action[2]
assert q == 132
for q, prev in [(111, 96), (130, 111), (150, 130), (172, 150), (204, 172)]:
    assert [key for key, action in table.items() if action[2] == q] == [(prev, 1)]
shared113 = sorted(key for key, action in changed.items() if action[2] == 113)
assert shared113 == [(98, 0), (175, 0), (176, 0), (236, 1)]
assert au.NEWPHYS == (6, 2, 0, 4, 3, 7, 8, 5, 1)

checks = []
def binding(path, digest):
    actual = sha(path)
    assert actual == digest, (str(path), digest, actual)
    checks.append({'path': str(path), 'sha256': actual})

pub = json.loads((WORK / 'publication.json').read_text())
for item in pub['files']:
    binding(item['path'], item['sha256'])
binding(pub['prior_raw_backend_packet']['path'], pub['prior_raw_backend_packet']['sha256'])
for field in ('original_driver', 'original_result'):
    item = pub['historical_timing_label_correction'][field]
    binding(item['path'], item['sha256'])
prior = json.loads(Path(pub['prior_raw_backend_packet']['path']).read_text())
for item in prior['files']:
    binding(item['path'], item['sha256'])
for path, digest in prior['outputs'].items():
    binding(path, digest)
results = json.loads((WORK / 'results.json').read_text())
source_paths = dict(driver=WORK/'check_mapping.py', table=table_path,
                    bisim254=RESEARCH/'bisim254.py',
                    Prog254=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Prog254.lean',
                    Dag254=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag254.lean',
                    strict=ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py')
for key, digest in results['inputs'].items():
    binding(source_paths[key], digest)
structure = json.loads((WORK/'structure-and-boot.json').read_text())
binding(WORK/'structure_and_boot.py', structure['driver_sha256'])
for item in structure['artifacts'].values():
    binding(item['path'], item['sha256'])
old = json.loads((WORK/'results-initial-timing-label.json').read_text())
def functional(r):
    r = json.loads(json.dumps(r))
    r['inputs'].pop('driver')
    r['conditional_symbolic'].pop('seconds', None)
    r['conditional_symbolic'].pop('combined_symbolic_and_blank_seconds', None)
    return r
assert functional(old) == functional(results)
assert results['conditional_symbolic']['passed'] == guards
assert results['conditional_symbolic']['failures'] == []
assert results['blank_control']['last_state'] == structure['bounded_whole_tape_roots']['last_state']
assert results['blank_control']['last_head'] == structure['bounded_whole_tape_roots']['last_head']
assert results['blank_control']['last_ones_count'] == structure['bounded_whole_tape_roots']['last_ones_count']
output = dict(status='PASS_INDEPENDENT_FINITE_ARTIFACT_CHECK',
              scope='Exact modified-source differences, preserved segment-certificate edges, context sharing, counts and provenance; no repeat symbolic or blank run, no Lean/compiler build.',
              driver={'path': str(Path(__file__)), 'sha256': sha(__file__)},
              publication_sha256=sha(WORK/'publication.json'),
              source_differences={'literal': pdiff, 'dag': ddiff},
              certificate={'pairs':len(cert),'distinct_pairs':len(cert),'reachable_pairs':len(seen),'halt_pairs':halt_pairs,'decrement_pairs':len(cert)-halt_pairs,'checked_successor_edges':edges,'root_segment_checked':True,'max_segment_increments_breaks_continues':max_segment},
              instruction_sites=len(sites), guarded_cases=guards,
              table={'working_states':252,'rows':504,'protected_pairs':55,'unchanged_protected_pairs':55,'logical_to_physical':au.NEWPHYS,'dispatch_chain':chain,'retained_incoming_113':shared113},
              timing_label_correction_functional_identity=True,
              hash_comparisons=len(checks),hash_checks=checks)
(WORK/'child-finite-check.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps({key:value for key,value in output.items() if key != 'hash_checks'}, indent=2))
