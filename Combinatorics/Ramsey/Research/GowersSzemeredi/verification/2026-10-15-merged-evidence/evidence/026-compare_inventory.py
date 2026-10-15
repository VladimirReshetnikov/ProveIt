"""Compare a later actual source inventory; never generate inventory or run native/Git."""
from pathlib import Path
from collections import Counter, defaultdict
import argparse, copy, datetime, hashlib, json, re, sys
sys.dont_write_bytecode = True
if sys.flags.optimize: raise RuntimeError('Assertions must remain enabled')
BASE = Path('/tmp/gowers-merged-inventory-normalization-tools')
ROOT = Path('/home/codex/.codex/worktrees/9c9b/Proofs')
SOURCE = ROOT / 'Combinatorics/Ramsey/Lean/GowersSzemeredi'
GENERATOR = ROOT / 'Combinatorics/Ramsey/scripts/gowers_status.py'
SOURCE_COMMIT = '466b09dd2e66b624e0cbd6e3cccf6cfe33a4b959'
BASELINE_SHA = '1d47298922976ab28977cdf338d37d2b3c202ebb6b9dc4b9df3972435635c8d9'
GENERATOR_SHA = '700dd07f230493eaec72a4ec460cf6d1d7e08a9333afab5165eb79dafd475cd1'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
canonical = lambda x: json.dumps(x, sort_keys=True, ensure_ascii=False)
def pairs(items):
    result = {}
    for k, v in items:
        assert k not in result, ('Duplicate JSON key', k)
        result[k] = v
    return result
def read(path): return json.loads(Path(path).read_text(), object_pairs_hook=pairs)
def pinned(path, expected):
    assert re.fullmatch('[0-9a-f]{64}', expected or '') and sha(path) == expected
    return read(path)
def when(value):
    t = datetime.datetime.fromisoformat(value); assert t.tzinfo is not None; return t

def differences(before, after, path=()):
    assert type(before) is type(after), ('JSON type changed', path)
    if isinstance(before, dict):
        assert list(before) == list(after), ('JSON keys/order changed', path)
        return [d for k in before for d in differences(before[k], after[k], path + (k,))]
    if isinstance(before, list):
        assert len(before) == len(after), ('Array length changed', path)
        return [d for i, (a, b) in enumerate(zip(before, after)) for d in differences(a, b, path + (i,))]
    return [] if before == after else [{'path': list(path), 'before': before, 'after': after}]

def array_order(before, raw, explicit=None):
    assert len(before) == len(raw), 'Companion occurrence count changed'
    for entry in before + raw:
        assert list(entry) == ['name', 'file', 'line'] and type(entry['name']) is str and type(entry['file']) is str
        assert type(entry['line']) is int and entry['line'] > 0
    assert Counter(e['name'] for e in before) == Counter(e['name'] for e in raw), 'Missing/new semantic companion occurrence'
    if explicit is not None:
        assert all(type(i) is int for i in explicit) and sorted(explicit) == list(range(len(raw))), 'Explicit order must be a bijection'
        assert all(before[i]['name'] == raw[j]['name'] for i, j in enumerate(explicit)), 'Explicit order changes semantic identity'
        return explicit
    order = [None] * len(before); remaining = set(range(len(raw)))
    # Preserve exact objects and repeated identical occurrences first.
    for i, entry in enumerate(before):
        match = next((j for j in sorted(remaining) if canonical(raw[j]) == canonical(entry)), None)
        if match is not None: order[i] = match; remaining.remove(match)
    names = dict.fromkeys(e['name'] for e in before)
    for name in names:
        bi = [i for i, e in enumerate(before) if e['name'] == name and order[i] is None]
        ri = [j for j in sorted(remaining) if raw[j]['name'] == name]
        for file in dict.fromkeys(before[i]['file'] for i in bi):
            left = [i for i in bi if before[i]['file'] == file]
            right = [j for j in ri if raw[j]['file'] == file]
            if len(left) == len(right) == 1:
                order[left[0]] = right[0]; remaining.remove(right[0])
        bi = [i for i in bi if order[i] is None]; ri = [j for j in ri if j in remaining]
        if not bi: continue
        if len(bi) == 1 or (len({canonical(before[i]) for i in bi}) == 1 and len({canonical(raw[j]) for j in ri}) == 1):
            for i, j in zip(bi, ri): order[i] = j; remaining.remove(j)
        else: raise AssertionError(('Ambiguous duplicate occurrence: supply inspected explicit index mapping', name, bi, ri))
    assert not remaining and sorted(order) == list(range(len(raw)))
    return order

def normalize(baseline, raw, mappings=None):
    assert list(baseline) == list(raw) and len(baseline['statements']) == len(raw['statements']) == 120
    assert [r['statement'] for r in baseline['statements']] == [r['statement'] for r in raw['statements']], 'Catalogue row order/identity changed'
    if mappings is not None: assert list(mappings) == ['arrays']
    mapping = {}; used = set()
    for item in (mappings or {'arrays': []})['arrays']:
        assert list(item) == ['path', 'raw_indices_in_baseline_order']
        key = tuple(item['path']); assert key not in mapping; mapping[key] = item['raw_indices_in_baseline_order']
    normalized = copy.deepcopy(raw); permutations = []
    for i, (old, new) in enumerate(zip(baseline['statements'], raw['statements'])):
        for collection in ('exact_companions', 'related_theorems'):
            path = ('statements', i, collection); explicit = mapping.get(path)
            if path in mapping: used.add(path)
            order = array_order(old[collection], new[collection], explicit)
            ordered = [copy.deepcopy(new[collection][j]) for j in order]
            assert Counter(map(canonical, ordered)) == Counter(map(canonical, new[collection])), 'Full objects/multiplicity must remain exact'
            normalized['statements'][i][collection] = ordered
            if order != list(range(len(order))): permutations.append({'path': list(path), 'raw_indices_in_baseline_order': order, 'occurrence_count': len(order), 'explicit_mapping': explicit is not None})
    assert used == set(mapping), 'Unused or unsupported explicit mapping path'
    changes = differences(baseline, normalized)
    for change in changes:
        p = change['path']
        allowed = (len(p) == 3 and p[0] == 'statements' and p[2] in ('file', 'line')) or (len(p) == 5 and p[0] == 'statements' and p[2] in ('exact_companions', 'related_theorems') and p[4] in ('file', 'line'))
        assert allowed, ('Semantic/scope/status/nonlocation change requires root inspection', change)
    return normalized, permutations, changes

def verify_locations(raw):
    cache = {}; pins = {}
    def content(entry, prefix):
        path = ROOT / entry['file']; assert path.resolve().parent == SOURCE.resolve() and path.suffix == '.lean'
        if path not in cache: cache[path] = path.read_text(); pins[str(path)] = sha(path)
        lines = cache[path].splitlines(); line = entry['line']; assert type(line) is int and 0 < line <= len(lines)
        text = '\n'.join(lines[line - 1:]); match = re.match(prefix, text); assert match, ('Source location/name mismatch', entry)
        return text, match
    for row in raw['statements']:
        name = row['statement']; content(row, r'^def ' + re.escape(name) + r'\s*:\s*Prop\s*:=')
        for collection in ('exact_companions', 'related_theorems'):
            for entry in row[collection]:
                assert re.fullmatch(re.escape(name) + r'_\w+', entry['name'])
                text, match = content(entry, r'^theorem ' + re.escape(entry['name']) + r'\b')
                header = text[match.end():].split(':=', 1)[0]
                exact = re.fullmatch(r'\s*:\s*' + re.escape(name) + r'\s*', header) is not None
                assert exact == (collection == 'exact_companions'), ('Generator classification changed', entry)
    return pins

def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('raw', 'generator-receipt', 'supplemental-receipt'): p.add_argument('--' + name, type=Path, required=True); p.add_argument('--' + name + '-sha256', required=True)
    p.add_argument('--mapping', type=Path); p.add_argument('--mapping-sha256'); p.add_argument('--output-dir', type=Path); p.add_argument('--write', action='store_true'); a = p.parse_args()
    assert sha(BASE / 'baseline.json') == BASELINE_SHA and sha(BASE / 'generator.py.txt') == sha(GENERATOR) == GENERATOR_SHA
    baseline = read(BASE / 'baseline.json'); raw = pinned(a.raw, a.raw_sha256)
    gen = pinned(a.generator_receipt, a.generator_receipt_sha256); supp = pinned(a.supplemental_receipt, a.supplemental_receipt_sha256)
    assert supp['status'] == 'passed' and supp['validation_mode'] == 'supplemental' and supp['source_commit'] == SOURCE_COMMIT
    assert type(supp['terminal_exit']) is int and supp['terminal_exit'] == 0 and supp['terminal_module_count'] == 437 and supp['terminal_module_count_matches'] is True and supp['contains_error_diagnostic'] is False
    assert gen['source_commit'] == SOURCE_COMMIT and gen['generator_sha256'] == GENERATOR_SHA
    assert type(gen['terminal_exit']) is int and gen['terminal_exit'] == 0
    assert len(gen['command']) == 2 and Path(gen['command'][0]).name.startswith('python') and gen['command'][1] == str(GENERATOR.relative_to(ROOT))
    assert Path(gen['raw_path']).resolve() == a.raw.resolve() and gen['raw_sha256'] == a.raw_sha256
    assert gen['supplemental_receipt_sha256'] == a.supplemental_receipt_sha256
    assert when(supp['final_evidence_checked_at']) <= when(gen['started_at']) <= when(gen['finished_at'])
    stderr = Path(gen['stderr_path']); assert sha(stderr) == gen['stderr_sha256'] and not stderr.read_bytes(), 'Nonempty generator stderr requires inspection'
    assert (a.mapping is None) == (a.mapping_sha256 is None)
    mapping = pinned(a.mapping, a.mapping_sha256) if a.mapping else None
    normalized, permutations, changes = normalize(baseline, raw, mapping); source_pins = verify_locations(raw)
    normalized_bytes = (json.dumps(normalized, indent=2) + '\n').encode(); normalized_sha = hashlib.sha256(normalized_bytes).hexdigest()
    evidence = {'status': 'PASS: source inventory content/location comparison only; no kernel certification', 'source_commit': SOURCE_COMMIT, 'baseline_source_inventory': {'path': str(BASE / 'baseline.json'), 'sha256': BASELINE_SHA}, 'raw_inventory': {'path': str(a.raw.resolve()), 'sha256': a.raw_sha256}, 'normalized_inventory_sha256': normalized_sha, 'row_count': 120, 'ordered_rows_preserved': True, 'all_raw_objects_and_duplicate_occurrences_preserved': True, 'permutations': permutations, 'location_leaf_changes': changes, 'location_leaf_change_count': len(changes), 'generator_receipt': {'path': str(a.generator_receipt.resolve()), 'sha256': a.generator_receipt_sha256}, 'supplemental_receipt_reference': {'path': str(a.supplemental_receipt.resolve()), 'sha256': a.supplemental_receipt_sha256}, 'explicit_mapping': {'path': str(a.mapping), 'sha256': a.mapping_sha256} if a.mapping else None, 'source_location_files': source_pins, 'kernel_evidence_revalidated': False, 'generator_invoked': False, 'helper_sha256': sha(__file__)}
    # Input/source race check; no repository writes in either mode.
    for path, h in {str(a.raw): a.raw_sha256, str(a.generator_receipt): a.generator_receipt_sha256, str(a.supplemental_receipt): a.supplemental_receipt_sha256, str(stderr): gen['stderr_sha256'], str(GENERATOR): GENERATOR_SHA, **source_pins}.items(): assert sha(path) == h
    if a.mapping: assert sha(a.mapping) == a.mapping_sha256
    if a.write:
        out = a.output_dir; assert out is not None and out.is_absolute() and out.resolve().is_relative_to(Path('/tmp')) and out.parent.is_dir() and not out.exists()
        out.mkdir()
        for name, data in [('raw.json', a.raw.read_bytes()), ('normalized.json', normalized_bytes), ('comparison.json', (json.dumps(evidence, indent=2) + '\n').encode())]:
            with (out / name).open('xb') as stream: stream.write(data)
        print(json.dumps({'status': evidence['status'], 'output_dir': str(out), 'files': {name: sha(out / name) for name in ('raw.json', 'normalized.json', 'comparison.json')}} , indent=2))
    else: print(json.dumps(evidence, indent=2))
if __name__ == '__main__': main()
