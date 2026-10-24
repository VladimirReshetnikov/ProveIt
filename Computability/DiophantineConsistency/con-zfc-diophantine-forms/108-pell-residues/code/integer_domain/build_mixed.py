#!/usr/bin/env python3
"""Build a mixed-domain quotient-restoration quartic.

The finite checks certify the literal sign propagation and integral projection.
The omitted quotient signs are justified by the accompanying arithmetic proof,
not inferred merely from a bounded calculation.
"""
from collections import Counter, defaultdict, deque
from copy import deepcopy
from pathlib import Path
import argparse, hashlib, json
import terminal_elimination as el
from sign_inference_original import square_root


def quotient_coordinates(source):
    variables = source['variables']
    quotients = {i for i, v in enumerate(variables)
                 if (v['name'].startswith('pow') and v['name'].endswith('.quotient'))
                 or (v['name'].startswith('index') and v['name'].endswith(('Squotient', 'Rquotient')))
                 or v['name'].endswith('.modular_quotient')
                 or v['name'] in ('shared_index.Bquotient', 'modular.root_quotient',
                                   'endpoint.u0', 'moduli_product.quotient',
                                   'crt.nonnegative_quotient')}
    signed = set(quotients) | {i for i, v in enumerate(variables)
                 if (v['name'].startswith('index') and v['name'].endswith(('.S','.R')))
                 or v['name'] == 'shared_index.U'}
    output_rows = []
    for rid, row in enumerate(source['residuals']):
        p = el.normalize(row['terms'])
        if row['label'] == 'multiplication' and any(i in quotients for m in p for i in m):
            outputs = [m[0] for m, c in p.items() if len(m) == 1 and c == 1]
            if len(outputs) != 1:
                raise ValueError('ambiguous quotient product gate')
            signed.update(outputs)
            output_rows.append({'row': rid, 'output': outputs[0]})
    return quotients, signed, output_rows


def infer(source, excluded):
    vs = source['variables']; rules = []
    for rid, row in enumerate(source['residuals']):
        p = el.normalize(row['terms'])
        for (v,), coef in [(m, c) for m, c in p.items() if len(m) == 1]:
            rest = {m: -c * (1 if coef > 0 else -1) for m, c in p.items() if m != (v,)}
            if any(v in m for m in rest):
                continue
            root = None
            if all(c >= 0 for c in rest.values()):
                deps = {k for m in rest for k, e in Counter(m).items() if e % 2}
                kind = 'positive_monomials'
            else:
                root = square_root(rest)
                if root is None:
                    continue
                deps = set(); kind = 'affine_square'
            rules.append((v, deps, rid, abs(coef), rest, kind, root))
    rev = defaultdict(list)
    for k, (_, deps, *_) in enumerate(rules):
        for d in deps:
            rev[d].append(k)
    def closure(seed):
        known = set(seed)
        pending = [len(deps - known) for v, deps, *_ in rules]
        queue = deque(i for i, n in enumerate(pending) if n == 0)
        proof = []
        while queue:
            k = queue.popleft()
            v, deps, rid, c, rest, kind, root = rules[k]
            if v in known or v in excluded:
                continue
            known.add(v)
            step = {'variable': v, 'name': vs[v]['name'], 'row': rid,
                    'coefficient': c, 'dependencies': sorted(deps),
                    'rhs': el.as_terms(rest), 'kind': kind}
            if root is not None:
                step['square_root'] = el.as_terms(root)
            proof.append(step)
            for k2 in rev[v]:
                pending[k2] -= 1
                if pending[k2] == 0:
                    queue.append(k2)
        return known, proof
    required = set(range(len(vs))) - excluded
    seed = {i for i, v in enumerate(vs)
            if v['kind'] not in ('gate', 'square_difference')} - excluded
    if not required <= closure(seed)[0]:
        raise ValueError('initial sign inference incomplete')
    initial = len(seed)
    for i in sorted(seed, reverse=True):
        if required <= closure(seed - {i})[0]:
            seed.remove(i)
    known, proof = closure(seed)
    if known != required:
        raise ValueError('incorrect mixed sign coverage')
    return {'initial_guards': initial, 'retained_guards': len(seed),
            'guard_indices': sorted(seed), 'required_nonnegative': sorted(required),
            'temporarily_signed': sorted(excluded), 'proof_steps': proof}


def build(source_path, output, cap, bound_path=None):
    source_bytes = Path(source_path).read_bytes()
    source = json.loads(source_bytes)
    qs, signed, product_rows = quotient_coordinates(source)
    positivity = infer(source, signed)
    if bound_path is not None:
        bounds=json.loads(Path(bound_path).read_text())
        if set(bounds['required_nonnegative']) != set(positivity['required_nonnegative']):
            raise ValueError('bound certificate required domain mismatch')
        if set(bounds['temporarily_signed']) != signed:
            raise ValueError('bound certificate signed domain mismatch')
        positivity['guard_indices']=bounds['seeds']
        positivity['retained_guards']=len(bounds['seeds'])
        positivity['proof_steps']=[]
        positivity['bound_steps']=bounds['steps']
        positivity['bounds']=bounds['bounds']
    integer = deepcopy(source)
    integer['domain'] = 'unrestricted integers'
    integer.pop('metrics', None)
    guards = []
    for v in positivity['guard_indices']:
        a, b, c = range(len(integer['variables']), len(integer['variables']) + 3)
        integer['variables'] += [{'name': f'nonnegative.{v}.{s}', 'kind': 'integer_guard'}
                                 for s in ('a', 'b', 'c')]
        integer['residuals'].append({'label': f'nonnegative.{v}',
            'terms': el.as_terms({(v,):1, (a,a):-1, (b,b):-1, (c,c):-1, (c,):-1})})
        guards.append({'variable': v, 'auxiliary': [a,b,c]})
    digest = lambda obj: hashlib.sha256(el.canonical_bytes(obj)).hexdigest()
    certificate = {'schema': 'pell_quotient_restoration_v1',
                   'source_sha256': digest(source), 'guarded_sha256': digest(integer),
                   'quotient_indices': sorted(qs), 'product_rows': product_rows,
                   'positivity': positivity, 'guards': guards}
    from check_mixed import domain
    domain(source, integer, certificate)
    target, projection, metrics = el.optimize(integer, max_support=cap)
    check = el.verify(integer, target, projection)
    directory = Path(output); directory.mkdir(parents=True, exist_ok=True)
    for name, obj in [('source.json', source), ('guarded.json', integer),
                      ('domain_certificate.json', certificate), ('equation.json', target),
                      ('elimination_certificate.json', projection),
                      ('expanded_polynomial.json', el.expand(target)),
                      ('METRICS.json', metrics | {'guards':len(guards),
                        'signed_source_coordinates':len(signed), 'quotients':len(qs),
                        'source_canonical_sha256': digest(source),
                        'projection_check':check})]:
        (directory / name).write_bytes(el.canonical_bytes(obj))
    return metrics | {'guards': len(guards), 'quotients': len(qs)}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--source', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--cap', type=int, default=16)
    p.add_argument('--bound-certificate',type=Path)
    args = p.parse_args()
    print(json.dumps(build(args.source, args.output, args.cap,args.bound_certificate), indent=2))
