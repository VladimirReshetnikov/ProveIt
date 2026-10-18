"""Own metadata-only source review of the frozen joint builder. Does not import it."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path('/tmp/zfc-joint-equational-packet')
REF = Path('/tmp/zfc-compare-d584512002/zfc242-contextual-reuse-20261018/zfc242-contextual-reuse-20261018/research/formalism_dispatch/reference')
HERE = Path(__file__).resolve().parent
checks = 0
files = {}


def check(ok, message):
    global checks
    checks += 1
    if not ok:
        raise ValueError(message)


def read(p, expected=None):
    data = p.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    check(expected is None or digest == expected, 'Changed pin: ' + str(p))
    files[str(p)] = {'path': str(p), 'sha256': digest, 'bytes': len(data)}
    return data


def freeze(t):
    return tuple(freeze(x) for x in t) if isinstance(t, list) else t


def rename(t, mapping):
    return mapping.get(t, t) if isinstance(t, str) else (t[0], *(rename(a, mapping) for a in t[1:]))


def clause(schema, mapping=None):
    prem, conclusion = schema
    mapping = mapping or {}
    return tuple((False, *rename(p, mapping)) for p in prem) + ((True, *rename(conclusion, mapping)),)


def main():
    builder = ROOT / 'build_joint.py'
    text = read(builder, 'c1b5c286c3bee735c9f0777a2535e35d7ac89c9e0894071de56e753cb55ce2ff').decode()
    read(ROOT / 'proof.md', 'e7b814406847a116351029b9f11cadd4ae6eb05738746dcefb204bace8c56bae')
    parsed = ast.parse(text)
    literal = {}
    for node in parsed.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id in ('PINS', 'HORN_SHA', 'PACKED'):
                    literal[target.id] = ast.literal_eval(node.value)
    check(set(literal) == {'PINS', 'HORN_SHA', 'PACKED'}, 'Missing frozen inputs')
    check(literal['PACKED'] == ('V', 'A', 'U', 'F'), 'Wrong packed function set')
    for name, digest in literal['PINS'].items():
        read(REF / name, digest)
    read(HERE / 'horn_certificates.py', literal['HORN_SHA'])
    horn = json.loads(read(HERE / 'horn-review.json'))
    check(horn['reviewer_source']['sha256'] == literal['HORN_SHA'], 'Horn receipt source differs')
    check(horn['certificate_count'] == 12 and horn['inference_count'] == 49 and horn['findings'] == [], 'Wrong Horn result')
    schemas = {k: freeze(v) for k, v in horn['schemas'].items()}
    source = freeze(json.loads(read(REF / 'FC13B_complete.json')))
    baseline = json.loads(read(REF / 'baseline_grouped.json'))
    check(source[13] == clause(schemas['refl']), 'Reflexivity mismatch')
    check(source[14] == clause(schemas['euclid']), 'Euclidean mismatch')
    check(source[16] == clause(schemas['C_full']), 'Full C mismatch')
    check(source[22] == clause(schemas['Inc_congr'], {'x': 'x0', 'u': 'y0', 'y': 'x1', 'v': 'y1'}), 'Inc mismatch')
    for index, symbol in [(15, 'V'), (18, 'A'), (19, 'U'), (20, 'F')]:
        check(source[index] == ((False, 'Eq', 'x0', 'y0'), (False, 'Eq', 'x1', 'y1'),
                                (True, 'Eq', (symbol, 'x0', 'x1'), (symbol, 'y0', 'y1'))), 'Dropped function congruence differs')
    check(source[21] == ((False, 'Eq', 'x0', 'y0'), (False, 'Eq', 'x1', 'y1'),
                         (False, 'E', 'x0', 'x1'), (True, 'E', 'y0', 'y1')), 'Removed E congruence differs')
    indices = [i for group in baseline['source_groups'] for i in group['source_indices']]
    check(sorted(indices) == list(range(23)) and len(indices) == 23, 'Baseline groups do not partition clauses')
    dropped = [group['source_indices'][0] for group in baseline['source_groups']
               if tuple(group['source_indices']) in ((15,), (16,), (18,), (19,), (20,), (21,))]
    check(dropped == [15, 16, 18, 19, 20, 21], 'Dropped group order differs')
    check(2 + 19 - len(dropped) + 2 + 1 == 18, 'Noalias equation census')
    check(2 + 19 - len(dropped) + 3 + 2 + 1 == 21, 'Alias equation census')
    old_sig = baseline['signature']
    sig = {s: a for s, a in old_sig.items() if s not in ('V', 'A', 'U', 'F', 'p_E', 'top')}
    sig.update({'tag_' + s: 0 for s in literal['PACKED']})
    sig['H'] = 3
    check(list(sig.items()) == [('d', 0), ('C', 3), ('I', 2), ('p_Inc', 2), ('p_Eq', 2), ('N', 2),
                               ('tag_V', 0), ('tag_A', 0), ('tag_U', 0), ('tag_F', 0), ('H', 3)], 'Signature order differs')
    # Finite AST call inventory distinguishes the codec/checker API from search.
    calls = [n for n in ast.walk(parsed) if isinstance(n, ast.Call)]
    attrs = sorted({n.func.attr for n in calls if isinstance(n.func, ast.Attribute)})
    check(not set(attrs) & {'search', 'optimized_equation', 'run', 'Popen', 'system'}, 'Unexpected execution/search call')
    imports = [n for n in ast.walk(parsed) if isinstance(n, (ast.Import, ast.ImportFrom))]
    check(all(not isinstance(n, ast.ImportFrom) or n.module == 'pathlib' for n in imports), 'Unexpected from-import')
    for path, pin in files.items():
        check(hashlib.sha256(Path(path).read_bytes()).hexdigest() == pin['sha256'], 'File changed at close')
    result = {'status': 'SOURCE_ONLY_JOINT_BUILDER_REVIEW_PASS', 'findings': [], 'checks': checks,
              'role': 'Independent builder/proof reviewer; authored the separately pinned Horn helper. No builder or supplied module execution.',
              'files': list(files.values()),
              'reviewer_source': {'path': str(Path(__file__)), 'sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
              'read_scope': ['All 249 builder lines', 'Full ordinary proof.md', 'Full two pinned inherited module sources',
                             'Exact 23 source clauses and 19 baseline groups', 'All independently authored Horn schemas/certificates'],
              'conclusions': ['Exact membership and fixed-selector packing terms agree with the mathematical definition.',
                              'Partition clauses bind to the helper; no selector-congruence premise is introduced.',
                              'Boolean checks occur before truth fusion; alias is a charged explicit term definition.',
                              'Root execution gates arity, baseline/full codec roundtrips, strict truncations, contextual orientations and input rehashes.',
                              'No measured joint packet bit count or actual builder PASS is claimed by this source review.']}
    (HERE / 'joint-builder-source-review.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'checks': checks, 'result_sha256': hashlib.sha256((HERE / 'joint-builder-source-review.json').read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
