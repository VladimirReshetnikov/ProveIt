#!/usr/bin/env python3
"""Exact Source151 omit-zero composition on submitted Source152 K217.

Checks source/physical binding and the prior complete startup trace. This is not
a full primitive runtime check or a proof-assistant theorem.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, os
import source_language as s
import build221 as b

HERE = Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def dump(p, x): p.write_text(json.dumps(x, indent=2, sort_keys=True) + '\n')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    assert __debug__ and not os.getenv('PYTHONOPTIMIZE')
    inputs = HERE / 'inputs'
    origins = load(HERE / 'input-origins.json')
    assert all(sha(inputs / n) == v['stored_sha256'] for n, v in origins.items())
    assert sha(inputs / 'parent.native.tm') == 'b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088'
    assert sha(inputs / 'parent.sites.json') == '9eac900e83742470893ea433cb0868e9ff6296f905cd6f3359b7a2c0e3114655'
    assert load(inputs / 'parent-actual.json')['status'] == 'FIVE_SELECTED_LEAVES_PASS'
    assert load(inputs / 'parent-runtime.json')['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
    files = [Path(__file__), HERE / 'source_language.py', HERE / 'build221.py', HERE / 'input-origins.json', *sorted(inputs.iterdir())]
    before = {str(p): sha(p) for p in files}
    a.output.mkdir(parents=True, exist_ok=False)

    oldrows = load(inputs / 'parent.sites.json')
    old = s.tree(oldrows)
    T = b.read_table((inputs / 'parent.native.tm').read_bytes())
    og, op = b.decoder_map(T, old)
    base = s.tree(load(inputs / 'source151-baseline.sites.json'))
    omit = s.tree(load(inputs / 'source151-omit.sites.json'))
    assert omit == s.replace(base, '11111', s.subtree(base, '111111'))
    parent = '111111'; deleted = parent + '0'; promoted = parent + '1'
    assert s.subtree(old, parent) == s.subtree(base, '11111')
    assert s.boundary(s.subtree(old, deleted)) == (0, 0, False)
    assert s.boundary(s.subtree(old, promoted)) == (0, 0, False)
    assert len(s.sites(s.subtree(old, deleted))) == 19
    assert len(s.sites(s.subtree(old, promoted))) == 7
    assert op[164] == ['11111'] and T[164, 1] == (1, 1, 98) and T[98, 1] == (1, 1, 114)
    new = s.replace(old, parent, s.subtree(old, promoted))
    newrows = s.sites(new)
    N = dict(T); N[164, 1] = (1, 1, 114)
    assert [k for k in T if T[k] != N[k]] == [(164, 1)]
    ng, np = b.decoder_map(N, new)
    oldstates = {p: q for q, ps in op.items() for p in ps}
    newstates = {p: q for q, ps in np.items() for p in ps}
    def previous_path(p):
        return promoted + p[len(parent):] if p.startswith(parent) else p
    for p, q in newstates.items():
        assert oldstates[previous_path(p)] == q, (p, q, previous_path(p))
    oldleaf = {p: (op_, arg) for p, op_, arg in oldrows}
    for p, op_, arg in newrows:
        original = previous_path(p)
        assert oldleaf[original] == (op_, arg)
        assert N[newstates[p[:-1]], int(p[-1])] == T[oldstates[original[:-1]], int(original[-1])]

    interval = [i for i, (p, _, _) in enumerate(oldrows) if p.startswith(deleted)]
    lo, hi = min(interval), max(interval) + 1
    assert interval == list(range(lo, hi)) and hi - lo == 19
    assert [x[1:] for x in newrows] == [x[1:] for x in oldrows[:lo] + oldrows[hi:]]
    graph0 = s.graph_arithmetic(oldrows)[0]
    graph1 = s.graph_arithmetic(newrows)[0]
    assert graph0 == s.graph_intervals(oldrows)
    assert graph1 == s.graph_intervals(newrows)
    def redirect(i):
        if lo <= i < hi:
            assert i == lo, ('nonentry deleted target', i)
            i = hi
        return i if i < lo else i - 19
    edge_count = 0
    for i, (effect, targets) in enumerate(graph0):
        if lo <= i < hi: continue
        j = i if i < lo else i - 19
        assert graph1[j] == [effect, [redirect(t) for t in targets]], (i, j)
        edge_count += len(targets)

    # Reconstruct the entire frozen parent trace from the blank tape, requiring
    # each modified-table action to equal the parent action along that trace.
    rawboot = gzip.decompress((inputs / 'parent-startup.json.gz').read_bytes())
    assert hashlib.sha256(rawboot).hexdigest() == origins['parent-startup.json.gz']['original_sha256']
    boot = json.loads(rawboot)
    assert boot['status'] == 'CALIBRATED_DIRTY_ROOT_SEED'
    assert len(boot['trace']) == boot['steps'] == 312617
    q, head, ones, changed_visits = 0, 0, set(), 0
    for tq, th, rd, w, d, z in boot['trace']:
        assert (tq, th, rd) == (q, head, int(head in ones))
        assert T[q, rd] == N[q, rd] == (w, d, z)
        changed_visits += int((q, rd) == (164, 1))
        if w: ones.add(head)
        else: ones.discard(head)
        q, head = z, head + d
    assert changed_visits == 0
    assert (q, head, sorted(ones)) == (boot['state'], boot['head'], boot['one_cells'])
    reach = {0}; todo = [0]
    for q in todo:
        for bit in (0, 1):
            z = N[q, bit][2]
            if z != 254 and z not in reach: reach.add(z); todo.append(z)
    assert reach == {q for q, _ in N} and len(N) == 434
    (a.output / 'candidate.native.tm').write_bytes(b.table_bytes(N))
    (a.output / 'source.sites.json').write_bytes(s.compact(newrows))
    assert before == {str(p): sha(p) for p in files}
    report = dict(
        status='EXACT_217_OMIT_ZERO_SOURCE_AND_STARTUP_COMPOSITION_PASS',
        table_sha256=sha(a.output / 'candidate.native.tm'), source_sha256=sha(a.output / 'source.sites.json'),
        working_states=len(N)//2, rows=len(N), metrics=s.metrics(new),
        guarded_cases=sum(2 if op_ == 'CD' else 1 for p, op_, arg in newrows),
        physical_patch=dict(row=[164, 1], old=T[164, 1], new=N[164, 1], parent_occurrences=op[164]),
        source_edit=dict(parent=parent, deleted=deleted, promoted=promoted, deleted_ordinal_interval=[lo, hi], deleted_leaves=19),
        whole_source_checks=dict(internal_nodes=len(newstates), all_leaf_actions_same_as_corresponding_prior_leaf=True,
            all_internal_prefix_paths_preserve_tape=True, expected_state_relation=True, two_independent_CFG_resolvers=True,
            retained_redirected_edges=edge_count),
        blank=dict(status='EXACT_FULL_BLANK_TRACE_UNCHANGED', steps=boot['steps'], changed_row_visits=changed_visits,
            state=boot['state'], head=boot['head'], one_cells=boot['one_cells']),
        scope='Exact closed-source deletion, expected decoder-state mapping, literal retained leaf actions, redirected full CFG, and complete prior blank trace replay. The Source151 ordinary proof compiler cleanup applies separately. No full arbitrary-natural runtime replay for the shortened source, new216 result, or proof-assistant endpoint.',
        inputs=before)
    dump(a.output / 'composition.json', report)
    print(json.dumps({k: v for k, v in report.items() if k not in ('inputs', 'blank')}, indent=2))

if __name__ == '__main__': main()
