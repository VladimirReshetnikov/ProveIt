#!/usr/bin/env python3
"""Remove precisely the two derived guards and generate complete Z projections."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import tempfile
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
NAMES = [('unprojected', 0), ('support4', 4), ('support8', 8),
         ('support16', 16), ('support32', 32)]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode()


def digest(data):
    return sha256(data).hexdigest()


def load(name):
    return json.loads((HERE / name).read_text())


def generate():
    pins = load('SOURCE_PINS.json')
    for name, pin in pins['sources'].items():
        need(digest((HERE / 'source' / name).read_bytes()) == pin['sha256'], 'immutable input ' + name)
    body = load('source/natural667.json')
    raw = load('source/raw_builder.json')
    old = load('source/route_sign.json')
    ids = {encoded(v): i for i, v in enumerate(raw['variables'])}
    retained = [ids[encoded(v)] for v in body['variables']]
    need(len(ids) == 1259 and len(retained) == 667, 'full metadata identities')
    need([(i, retained[i]) for i in [0, 294, 326, 461]] ==
         [(0, 0), (294, 644), (326, 694), (461, 917)], 'actual retained t0,A,T,D')
    seeds = [v for v in old['guards'] if retained[v] not in {644, 917}]
    need(len(old['guards']) == 109 and len(seeds) == 107, 'only A/D guards omitted')
    equation = deepcopy(body)
    equation['domain'] = 'unrestricted integers'
    equation['variant'] = 'mixed667_107_guards_derived_A_D'
    equation.pop('metrics', None)
    guards = []
    for j, v in enumerate(seeds):
        a, b, c = range(667+3*j, 670+3*j)
        equation['variables'].extend(dict(kind='nonnegative_guard', name='guard.'+str(v)+'.'+s)
                                     for s in ['a', 'b', 'c'])
        equation['residuals'].append(dict(label='guard.'+str(v),
            terms=[[1, [v]], [-1, [a,a]], [-1, [b,b]], [-1, [c]], [-1, [c,c]]]))
        guards.append(dict(variable=v, raw_variable=retained[v], auxiliary=[a,b,c]))
    cert = dict(schema='contracted_mixed107_bounds_v1', seed_indices=seeds,
        retained_raw_indices=retained, guards=guards,
        removed_guards=[dict(variable=v, raw_variable=retained[v]) for v in [294,461]],
        required_seed_identities=[dict(variable=v, raw_variable=retained[v]) for v in [0,326]],
        bound_steps=load('source/four_bounds.json'))
    old_positions = {v:j for j,v in enumerate(old['guards'])}
    bridge = dict(schema='contracted988_to_literal994_v1',
        shared_body_coordinates=667, shared_body_rows=585,
        shared_guard_transfers=[dict(variable=g['variable'], raw_variable=g['raw_variable'],
            source_auxiliary=g['auxiliary'], target_auxiliary=list(range(
                667+3*old_positions[g['variable']],670+3*old_positions[g['variable']]))) for g in guards],
        new_994_guard_triples=[dict(variable=v, raw_variable=retained[v],
            target_auxiliary=list(range(667+3*old_positions[v],670+3*old_positions[v]))) for v in [294,461]],
        statement='Restore all592 raw affine wires over Z; four original-row bounds derive A,D>=2. Supply six fresh guard witnesses, then invoke the sealed literal994 existential theorem. Reverse by forgetting exactly those six witnesses.')
    files = {'domain_certificate.json': encoded(cert), 'BRIDGE994.json': encoded(bridge)}
    archive = REPO / pins['arithmetic_archive']
    need(digest(archive.read_bytes()) == pins['arithmetic_archive_sha256'], 'complete arithmetic archive')
    member = 'ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
    census = {}
    with zipfile.ZipFile(archive) as z, tempfile.TemporaryDirectory(prefix='mixed988-project-') as tmp:
        source = z.read(member)
        need(digest(source) == pins['read_source_members'][member], 'literal generic signed producer')
        path = Path(tmp) / 'terminal_elimination.py'; path.write_bytes(source)
        spec = importlib.util.spec_from_file_location('mixed988_optimizer', path)
        engine = importlib.util.module_from_spec(spec); spec.loader.exec_module(engine)
        p = engine.expand(equation)
        equation['metrics'] = dict(variables=len(equation['variables']), quadratic_rows=len(equation['residuals']),
            exact_degree=max(len(m) for c,m in p['terms']), expanded_monomials=len(p['terms']),
            max_abs_expanded_coefficient=max(abs(c) for c,m in p['terms']))
        files['guarded.json'] = encoded(equation)
        for name, cap in NAMES:
            child, projection, metrics = engine.optimize(equation, max_support=cap)
            need(projection['unconstrained_removed'] == [], 'every signed parent coordinate restored')
            review = engine.verify(equation, child, projection)
            for filename, value in [('equation.json', child), ('elimination_certificate.json', projection),
                ('expanded_polynomial.json', engine.expand(child)),
                ('BUILD.json', dict(metrics=metrics, producer_internal_verification=review, support_cap=cap))]:
                files[name+'/'+filename] = encoded(value)
            census[name] = dict(metrics=child['metrics'], support_cap=cap,
                eliminated_coordinates=len(projection['steps']), unconstrained_removed=[])
    files['CENSUS.json'] = encoded(census)
    files['BUILD.json'] = encoded(dict(status='PASS', generator_sha256=digest(Path(__file__).read_bytes()),
        sha256={n:digest(d) for n,d in files.items()},
        scope='Literal988 integer quartic and fresh signed projections; only two derived A/D guard triples removed.'))
    return files, census


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--check',action='store_true')
    args=parser.parse_args(); files,census=generate()
    for name,data in files.items():
        path=HERE/name
        if args.check:
            need(path.read_bytes()==data,'complete deterministic artifact '+name)
        else:
            path.parent.mkdir(parents=True,exist_ok=True); path.write_bytes(data)
    print(json.dumps(dict(status='PASS',check=args.check,metrics={n:d['metrics'] for n,d in census.items()}),indent=2))


if __name__=='__main__': main()
