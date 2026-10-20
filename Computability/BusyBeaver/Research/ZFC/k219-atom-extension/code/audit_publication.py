"""Metadata/literal audit of two research packets; no search or simulation."""
from pathlib import Path
import argparse
import ast
import collections
import gzip
import hashlib
import json
import re

ATOM = Path(__file__).resolve().parent.parent
CONT = ATOM.parent / 'k219-continuation-search'
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_text())
frozen = lambda x: tuple(map(frozen, x)) if isinstance(x, list) else x


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    provenance = read(ATOM / 'provenance.json')
    for row in provenance['mapping']:
        data = (ATOM / row['destination']).read_bytes()
        assert sha(data) == row['stored_sha256']
        raw = gzip.decompress(data) if row['encoding'] == 'gzip' else data
        assert sha(raw) == row['original_sha256']
    history = json.loads(gzip.decompress((ATOM / 'history/scratch-texts.json.gz').read_bytes()))
    for row in history.values():
        assert sha(row['text'].encode()) == row['sha256']
    library = read(ATOM / 'results/library-review.json')
    assert library['atoms'] == 19 and library['control_entries'] == 1400
    assert all(x['signatures_equal'] and x['in_new_library'] for x in library['controls'])
    assert sha((ATOM / 'code/library.py').read_bytes()) == library['interpreter_sha256']
    assert sha((ATOM / 'inputs/atoms.json').read_bytes()) == library['atoms_sha256']
    assert sha((ATOM / 'inputs/atoms.in').read_bytes()) == library['signatures_sha256']
    old = frozen(read(ATOM.parents[4] / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/140-k219-machine-new_equality_macro.json'))
    costs = []
    for cost in (4, 5):
        directory = ATOM / f'results/cost{cost}'
        execution = read(directory / 'execution.json')
        assert execution['status'] == 'COMPLETE' and execution['exit_code'] == 0
        assert execution['limits']['stored_nodes'] == 800000
        assert execution['limits']['root_cost'] == cost and execution['limits']['max_intermediate_cost'] == cost - 1
        assert execution['limits']['process_seconds'] == 110
        log = (directory / 'stdout.log').read_bytes()
        recipes = gzip.decompress((directory / 'nodes.gz').read_bytes())
        assert sha(log) == execution['log_sha256'] and sha(recipes) == execution['nodes_sha256']
        for name, path in [('search.cpp', ATOM / 'code/search.cpp'), ('library.py', ATOM / 'code/library.py'), ('atoms.in', ATOM / 'inputs/atoms.in'), ('atoms.json', ATOM / 'inputs/atoms.json')]:
            assert sha(path.read_bytes()) == execution['inputs'][name]
        nodes = list(map(frozen, read(ATOM / 'inputs/atoms.json')))
        roots = []
        for line in recipes.decode().splitlines():
            words = line.split()
            if words[0] == 'H':
                a, b, c = map(int, words[1:])
                assert c == cost and a < len(nodes) and b < len(nodes)
                roots.append((nodes[a], nodes[b]))
            else:
                i, a, b, c = map(int, words)
                assert i == len(nodes) and a < i and b < i and c < cost
                nodes.append((nodes[a], nodes[b]))
        intermediate = [int(i) for i in re.findall(r'^HIT (\d+) cost ', log.decode(), re.M)]
        expected = list(dict.fromkeys([nodes[i] for i in intermediate] + roots))
        analysis = json.loads(gzip.decompress((directory / 'analysis.json.gz').read_bytes()))
        assert analysis['stored_nodes'] == len(nodes) < 800000
        assert analysis['reported_hits'] == len(intermediate) + len(roots)
        assert analysis['unique_macros'] == len(expected) == len(analysis['results'])
        for i, result in enumerate(analysis['results']):
            assert result['id'] == i and result['literal_replacements'] == 4
            assert frozen(result['macro']) == expected[i]
        census = {str(k): v for k, v in collections.Counter(x['metrics']['dag_nodes'] for x in analysis['results']).items()}
        assert census == analysis['dag_census']
        assert min(int(k) for k in census) == 206 and census['206'] == 1
        assert all(frozen(x['macro']) == old for x in analysis['results'] if x['metrics']['dag_nodes'] == 206)
        assert read(directory / 'census.json') == {k: v for k, v in analysis.items() if k != 'results'}
        costs.append({'cost': cost, 'nodes': len(nodes), 'hits': len(expected), 'minimum_dag': 206})
    reconstruction = read(ATOM / 'results/reconstruction-control.json')
    assert reconstruction['status'] == 'LITERAL_RECONSTRUCTION_PASS'
    assert reconstruction['source_sha256'] == library['source']['sha256']
    assert reconstruction['reconstructor_sha256'] == sha((ATOM / 'code/reconstruct.py').read_bytes())
    continuation = read(CONT / 'results/start-blank-provenance.json')
    scratch = json.loads(gzip.decompress((CONT / 'history/start-and-blank-scratch.json.gz').read_bytes()))
    for path, row in scratch['files'].items():
        text = scratch['text_by_sha256'][row['sha256']]
        assert sha(text.encode()) == row['sha256'] and len(text.encode()) == row['bytes']
    for row in continuation['mapping']:
        if 'destination' in row:
            assert sha((CONT / row['destination']).read_bytes()) == row['sha256']
        else:
            assert sha((CONT / row['portable_source']).read_bytes()) == row['portable_sha256']
            assert scratch['files'][row['original_source']]['sha256'] == row['original_sha256']
    start = read(CONT / 'results/start-states-run1/result.json')
    assert start['status'] == 'COMPLETE_START_FOLD_SEARCH' and start['attempted'] == 19184 and not start['hits']
    assert sha((CONT / 'results/start-states-run1/rejections.jsonl.gz').read_bytes()) == start['rejections_sha256']
    counts = collections.Counter()
    with gzip.open(CONT / 'results/start-states-run1/rejections.jsonl.gz', 'rt') as stream:
        for i, line in enumerate(stream, 1):
            row = json.loads(line)
            assert row['id'] == i and row['drop'] == 0 and row['new_start'] == row['keep'] != 0
            counts[row['seed']] += 1
    assert i == 19184 and set(counts.values()) == {9592}
    for seed in start['seeds']:
        assert len(seed['states']) == len({s['keep'] for s in seed['states']}) == 218
        assert all(s['status'] == 'COMPLETE' and s['candidate_count'] == s['attempted'] == s['filter_rejections'] for s in seed['states'])
    blank = read(CONT / 'results/blank-domain-run1/result.json')
    assert [(s['all_contexts'], s['blank_contexts']) for s in blank['seeds']] == [(1012111, 999869), (1012495, 1000253)]
    assert all(len(s['changed_rows']) == 16 for s in blank['seeds'])
    rescreen = read(CONT / 'results/blank-rescreen-run1/result.json')
    assert rescreen['status'] == 'COMPLETE_BLANK_RESCREEN' and rescreen['rescreened'] == 0 and not rescreen['hits']
    assert sum(s['processed'] for s in rescreen['families']) == 326014
    assert all(s['status'] == 'COMPLETE' and s['candidate_count'] == s['processed'] == s['retained_prior_rejection'] for s in rescreen['families'])
    assert gzip.open(CONT / 'results/blank-rescreen-run1/rescreened.jsonl.gz', 'rb').read() == b''
    python_files = list((ATOM / 'code').glob('*.py')) + [CONT / n for n in ('search_start_states.py', 'compare_blank_domain.py', 'blank_domain.py', 'rescreen_blank_failures.py')]
    for path in python_files:
        ast.parse(path.read_text())
    links = []
    for root in (ATOM, CONT):
        for link in re.findall(r'\]\(([^)]+)\)', (root / 'README.md').read_text()):
            if not link.startswith(('http:', 'https:', '#')):
                target = root / link.split('#')[0]
                assert target.exists(), target
                links.append(str(target))
    record = {'status': 'PUBLICATION_METADATA_AND_LITERAL_RECIPES_PASS',
              'role': 'Author metadata audit; no new search, simulation or all-natural proof.',
              'costs': costs, 'start_specs': 19184, 'blank_retained_failures': 326014,
              'python_sources_parsed': len(python_files), 'local_links_checked': len(links),
              'script_sha256': sha(Path(__file__).read_bytes()),
              'readme_sha256': {str(r.name): sha((r / 'README.md').read_bytes()) for r in (ATOM, CONT)}}
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
