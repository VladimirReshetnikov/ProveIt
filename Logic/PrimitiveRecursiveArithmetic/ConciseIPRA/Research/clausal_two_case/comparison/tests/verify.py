"""Reproduce CE5-2 translations, adversarial checks, and exact measurements.

The checker is complete and standalone. This script is untrusted test code;
finite tests do not establish the universal mathematical equivalence theorem.
"""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
from translate import load, new, nodes, old, transform, translate


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def accepts(checker, certificate):
    try:
        return checker.verify(certificate) is True
    except Exception:
        return False


def root(p, q):
    return ['v', p, q]


def refl(t):
    return ['r', t]


def zero(a, h):
    return ['v', refl(a), refl([0, a, h])]


def sym(p, context=(), scope=0):
    s, t = old.derive(p, list(context), scope)
    return root(refl(s), p)


def trans(p, q, context=(), scope=0):
    return root(q, sym(p, context, scope))


def cong(h, p, context=(), scope=0):
    s, t = old.derive(p, list(context), scope)
    a = [0, s, h]
    b = [[0, 0], s, h]
    first = ['v', ['v', refl(s), refl(a)], refl(b)]
    second = ['v', p, refl(a)]
    return ['v', second, first]


def cert(proof):
    return {'goal': old.derive(proof, [], 0), 'proof': proof}


def metrics(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    if tree.body and isinstance(tree.body[0], ast.Expr) and isinstance(tree.body[0].value, ast.Constant) and isinstance(tree.body[0].value.value, str):
        tree.body.pop(0)
    normalized = (ast.unparse(tree) + '\n').encode()
    significant = sum(t.type not in {tokenize.ENCODING, tokenize.ENDMARKER,
                         tokenize.NEWLINE, tokenize.NL, tokenize.INDENT,
                         tokenize.DEDENT, tokenize.COMMENT}
                      for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    packed = gzip.compress(normalized, compresslevel=9, mtime=0)
    path.with_name(path.stem + '.normalized.py').write_bytes(normalized)
    path.with_name(path.stem + '.normalized.py.gz').write_bytes(packed)
    return {'program': path.name, 'raw_bytes': len(raw),
            'normalized_bytes': len(normalized), 'tokens': significant,
            'ast_nodes': sum(1 for _ in ast.walk(tree)), 'gzip9_bytes': len(packed),
            'raw_gzip9_bytes': len(gzip.compress(raw, compresslevel=9, mtime=0)),
            'sha256': hashlib.sha256(raw).hexdigest(),
            'normalized_sha256': hashlib.sha256(normalized).hexdigest()}


def dump(directory, name, value):
    folder = ROOT / 'certificates' / directory
    folder.mkdir(exist_ok=True, parents=True)
    (folder / (name + '.json')).write_text(json.dumps(value, indent=2) + '\n')


def main():
    inherited = {p.stem: json.loads(p.read_text()) for p in
                 sorted((ROOT / 'certificates' / 'upstream_positive').glob('*.json'))}
    rejects = {p.stem: json.loads(p.read_text()) for p in
               sorted((ROOT / 'certificates' / 'upstream_negative').glob('*.json'))}
    require(len(inherited) == 32 and len(rejects) == 24, 'upstream corpus is incomplete')
    additional = {}
    r0, r1 = refl(0), refl([0, 0])
    additional['direct_root_zero'] = cert(root(r0, r0))
    additional['direct_root_successor'] = cert(root(r1, r1))
    a = [0, [0, 0], [1, 0, 2]]
    additional['direct_root_iterator'] = cert(root(refl(a), refl(a)))
    p = zero([0, 0], [1, 0, [0, 2]])
    additional['symmetry_nontrivial'] = cert(sym(p))
    additional['transitivity_nontrivial'] = cert(trans(p, sym(p)))
    templates = [1, [0, 1], [1, 1, [2, 1, [0, 3]]],
                 [[1, 0, [0, 2]], 1, [2, 1, [0, 3]]],
                 [0, 1, [2, 1, [0, 3]]]]
    for i, h in enumerate(templates):
        additional['nested_congruence_' + str(i)] = cert(cong(h, p))
        hs, ht = old.derive(cong(h, p), [], 0)
        additional['nested_transport_' + str(i)] = cert(root(cong(h, p), refl(hs)))
    source = dict(inherited)
    source.update(additional)
    records = []
    translated = {}
    for name, data in source.items():
        target, stat = translate(data)
        require(target['goal'] == data['goal'], 'changed goal: ' + name)
        require(stat['new_nodes'] == stat['old_nodes'] + 2 * stat['root_nodes'], 'bad count')
        require(accepts(old, target) and accepts(new, target), 'translation failed: ' + name)
        translated[name] = target
        dump('positive', name, target)
        if name in additional:
            dump('additional_source', name, data)
        records.append(dict(name=name, **stat))

    # Explicit obsolete proofs are valid old certificates but rejected by the
    # new grammar. Their goals remain theorems; their translated proofs accept.
    obsolete = {name: additional[name] for name in
                ('direct_root_zero', 'direct_root_successor', 'direct_root_iterator',
                 'symmetry_nontrivial', 'transitivity_nontrivial')}
    for name, data in obsolete.items():
        require(accepts(old, data) and not accepts(new, data), 'root deletion not enforced')
        dump('obsolete', name, data)

    # All 24 inherited malformed or invalid proofs must reject unchanged.
    for name, data in rejects.items():
        require(not accepts(old, data), 'upstream negative unexpectedly accepted')
        require(not accepts(new, data), 'negative accepted: ' + name)
        try:
            translate(data)
        except Exception:
            pass
        else:
            raise RuntimeError('translator accepted invalid input: ' + name)

    # Four attacks alter the frame, or its selected computation case.
    good = copy.deepcopy(translated['direct_root_zero'])
    attack = copy.deepcopy(good)
    attack['proof'][2][2] = refl([0, [0, 0], 0])
    rejects['frame_wrong_initializer'] = attack
    attack = copy.deepcopy(good)
    attack['proof'][2][2] = refl([[0, 0], 0, 0])
    rejects['frame_wrong_counter'] = attack
    attack = copy.deepcopy(good)
    attack['proof'][2][2] = refl([0, 0, 2])
    rejects['frame_loose_bound_variable'] = attack
    attack = copy.deepcopy(good)
    attack['proof'][2][2] = refl([0, -1, 0])
    rejects['frame_fresh_parameter_escape'] = attack
    for name, data in rejects.items():
        require(not accepts(new, data), 'attack accepted: ' + name)
        dump('negative', name, data)

    # Open contexts: arbitrary equation assumptions and deeper rigid scopes.
    open_records = []
    context = [([0, 0], [-1, -2]), ([0, 0], [-1, -3])]
    p = ['u', 0, 0, refl(0)]
    q = ['u', 1, 0, refl(0)]
    open_proofs = {'three_parameter_root': root(p, q)}
    for i, h in enumerate(templates):
        proof = cong(h, p, context, 3)
        hs, ht = old.derive(proof, context, 3)
        open_proofs['nested_open_transport_' + str(i)] = root(proof, refl(hs))
    for name, proof in open_proofs.items():
        target, k = transform(proof, context, 3)
        expected = old.derive(proof, context, 3)
        require(new.derive(target, context, 3) == expected, 'open formula mismatch')
        require(nodes(target) == nodes(proof) + 2 * k, 'open count mismatch')
        record = {'name': name, 'context': context, 'scope': 3,
                  'goal': expected, 'source': proof, 'translated': target,
                  'old_nodes': nodes(proof), 'root_nodes': k, 'new_nodes': nodes(target)}
        dump('open', name, record)
        open_records.append({key: record[key] for key in
                             ('name', 'old_nodes', 'root_nodes', 'new_nodes')})

    measures = [metrics(ROOT / 'code' / (name + '.py')) for name in ('control', 'checker')]
    normalized = load('ce5_normalized', ROOT / 'code' / 'checker.normalized.py')
    for data in translated.values():
        require(accepts(normalized, data), 'normalized source rejected positive')
    for data in rejects.values():
        require(not accepts(normalized, data), 'normalized source accepted negative')

    # Public acceptance paths: normal/optimized, readable/normalized modules.
    runs = 0
    for optimized in (False, True):
        for filename in ('checker.py', 'checker.normalized.py'):
            for name, data, expected in (
                    [(n, d, True) for n, d in translated.items()] +
                    [(n, d, False) for n, d in rejects.items()] +
                    [(n, d, False) for n, d in obsolete.items()]):
                command = [sys.executable] + (['-O'] if optimized else [])
                command.append(str(ROOT / 'code' / filename))
                run = subprocess.run(command, input=json.dumps(data), text=True,
                                     capture_output=True, timeout=15)
                require((run.returncode == 0) == expected, 'CLI return mismatch: ' + name)
                require(run.stdout == ('ACCEPT\n' if expected else 'REJECT\n'),
                        'CLI stdout mismatch: ' + name)
                runs += 1

    result = {'python': sys.version, 'inherited_positive': len(inherited),
              'inherited_negative': 24, 'additional_positive': len(additional),
              'translated_positive': len(translated), 'negative': len(rejects),
              'obsolete_valid_old_certificates': len(obsolete),
              'open_context_tests': len(open_records), 'public_cli_runs': runs,
              'total_eliminated_root_nodes': sum(r['root_nodes'] for r in records),
              'exact_node_identity': 'new_nodes = old_nodes + 2 * root_nodes',
              'all_passed': True, 'translations': records,
              'open_translations': open_records, 'metrics': measures,
              'limitations': ['Finite tests are not a universal correctness proof.',
                  'The new kernel and translator are not formalized in Lean/Rocq.',
                  'The change does not beat the historical compact 516-byte codec.']}
    (ROOT / 'evidence' / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in
                    ('translations', 'open_translations', 'limitations')}, indent=2))


if __name__ == '__main__':
    main()
