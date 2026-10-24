#!/usr/bin/env python3
"""Research-only paired coefficient census; no builder/emitter execution.

Extracts and imports only the hash-authenticated, previously reviewed signed
terminal optimizer. All source equations are immutable JSON inputs. Each
whole integer projection is verified; the quartic is independently expanded.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import zipfile
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
ARCHIVE = 'docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip'
ARCHIVE_HASH = '59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59'
MEMBER = 'ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py'
MEMBER_HASH = '73ca399b859116cedd9b2b7cb107c82926421697f41ee63b9b61f8bc6c1c0027'
FILES = {
    'research/bootstrap-guard-exchange/README.md': '829b7125dfa1ba9074cc4b93eb247562bebdbc7d7ace0c4edf2b7c1981b8fff3',
    'candidates/projected-radius-mixed-bounds/source/raw_builder.json': '2dc3a2acaeb95d09b22501ee4e978327c03c2cd50a1a0817eadda257651a0a75',
    'candidates/projected-radius-comparison-base/domain_certificate.json': 'dc59fc01c077806a8e74f4f6dc455631ee0901843aa4d711aa2a3af9e79f13d5',
}
EXTRA = [
    'candidates/projected-radius-comparison-base/guarded.json',
    'candidates/projected-radius-comparison-base/CENSUS.json',
    'candidates/projected-radius-mixed-bounds/source/raw_restoration.json',
    'candidates/projected-radius-comparison-base/SOURCE_PINS.json',
    'reviews/bootstrap-guard-exchange-peer.md',
    'reviews/bootstrap-guard-exchange-peer.py',
    'reviews/bootstrap-guard-exchange-peer.json',
    'reviews/bootstrap-guard-exchange-peer_OPTIMIZED.json',
]

def need(value, message):
    if not value:
        raise ValueError(message)

def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()

def digest(data):
    return sha256(data).hexdigest()

def load(relative):
    return json.loads((ROOT / relative).read_bytes())

def sparse(terms):
    result = defaultdict(int)
    for c, m in terms:
        result[tuple(sorted(m))] += c
    return {m:c for m,c in result.items() if c}

def independent_expansion(equation):
    """Collect every ordered monomial product in every complete residual square."""
    result = defaultdict(int)
    for row in equation['residuals']:
        terms = sparse(row['terms'])
        for m, c in terms.items():
            for n, d in terms.items():
                result[tuple(sorted(m+n))] += c*d
    return [[c,list(m)] for m,c in sorted(result.items()) if c]

def make_inputs():
    old = load('candidates/projected-radius-comparison-base/domain_certificate.json')
    compact = load('candidates/projected-radius-comparison-base/guarded.json')
    # Remove copied census metadata from both inputs: the new guard has a different
    # expansion, and every reported output census is recomputed from its rows.
    compact.pop('metrics', None)
    restore = load('candidates/projected-radius-mixed-bounds/source/raw_restoration.json')
    compact_z = restore['retained_raw_indices'].index(645)
    compact_T = restore['retained_raw_indices'].index(694)
    need((compact_z, compact_T) == (295,326), 'literal raw/compact interface')
    record = next(g for g in old['guards'] if g['raw_variable'] == 694)
    need(record == dict(variable=326,raw_variable=694,auxiliary=[853,854,855]),
         'whole old guard record')
    compact_new = deepcopy(compact)
    target = [i for i,row in enumerate(compact_new['residuals']) if row['label'] == 'guard.326']
    need(len(target) == 1, 'unique compact guard row')
    row_index = target[0]
    expected = [[1,[326]],[-1,[853,853]],[-1,[854,854]],[-1,[855]],[-1,[855,855]]]
    need(compact_new['residuals'][row_index]['terms'] == expected, 'complete original compact guard polynomial')
    compact_new['residuals'][row_index]['terms'][0] = [1,[compact_z]]
    # Keep labels and all variable metadata identical to avoid heuristic confounds.
    need([i for i,(a,b) in enumerate(zip(compact['residuals'],compact_new['residuals'])) if a != b]
         == [row_index], 'only the guard value changes in the compact family')
    raw = load('candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    raw_old = dict(schema='finite_quadratic_residuals_v1',domain='unrestricted integers',
                   variables=deepcopy(raw['variables']),
                   residuals=[dict(label='raw.'+str(i)+'.'+row['label'],terms=deepcopy(row['terms']))
                              for i,row in enumerate(raw['rows'])],
                   polynomial='sum(square(row) for row in residuals)')
    guard_records = []
    for j, guard in enumerate(old['guards']):
        v = guard['raw_variable']
        a,b,c = range(len(raw['variables'])+3*j,len(raw['variables'])+3*j+3)
        raw_old['variables'].extend(dict(kind='nonnegative_guard',name='guard.raw'+str(v)+'.'+s)
                                    for s in ('a','b','c'))
        raw_old['residuals'].append(dict(label='guard.raw'+str(v),
            terms=[[1,[v]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]]))
        guard_records.append(dict(raw_variable=v,auxiliary=[a,b,c]))
    raw_new = deepcopy(raw_old)
    raw_row = next(i for i,row in enumerate(raw_new['residuals']) if row['label'] == 'guard.raw694')
    need(raw_new['residuals'][raw_row]['terms'][0] == [1,[694]], 'literal raw T0 guard')
    raw_new['residuals'][raw_row]['terms'][0] = [1,[645]]
    need(len(raw_old['variables']) == 1493 and len(raw_old['residuals']) == 1255,
         'complete raw source plus78 private triples')
    need([i for i,(a,b) in enumerate(zip(raw_old['residuals'],raw_new['residuals'])) if a != b]
         == [raw_row], 'only the guard value changes in the raw family')
    return {'compact78': {'baseline':compact,'exchanged':compact_new},
            'raw78': {'baseline':raw_old,'exchanged':raw_new}}, dict(
                compact_old=compact_T,compact_new=compact_z,compact_guard_row=row_index,
                raw_old=694,raw_new=645,raw_guard_row=raw_row,
                raw_guard_order=[g['raw_variable'] for g in guard_records],
                all_private_guard_indices_and_all_other_rows_unchanged=True,
                guarded_compact_variables=901,guarded_compact_rows=663,
                guarded_raw_variables=1493,guarded_raw_rows=1255)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE/'PROFILE.json')
    parser.add_argument('--family',choices=('compact78','raw78'),action='append')
    parser.add_argument('--caps',type=int,nargs='+',default=[0,4,8,16,32])
    args = parser.parse_args()
    pins = dict(FILES)
    for name, expected in FILES.items():
        need(digest((ROOT/name).read_bytes()) == expected, 'whole reviewed source '+name)
    for name in EXTRA:
        pins[name] = digest((ROOT/name).read_bytes())
    pins[str(Path(__file__).relative_to(ROOT))] = digest(Path(__file__).read_bytes())
    archive = REPO / ARCHIVE
    need(digest(archive.read_bytes()) == ARCHIVE_HASH, 'whole arithmetic archive')
    with zipfile.ZipFile(archive) as z:
        source = z.read(MEMBER)
    need(digest(source) == MEMBER_HASH, 'authenticated optimizer member')
    inputs, exchange = make_inputs()
    census = load('candidates/projected-radius-comparison-base/CENSUS.json')
    existing_names = {0:'unprojected',4:'support4',8:'support8',16:'support16',32:'support32'}
    records = []
    with tempfile.TemporaryDirectory(prefix='bootstrap-guard-coefficient-profile-') as tmp:
        path = Path(tmp)/'terminal_elimination.py'
        path.write_bytes(source)
        spec = importlib.util.spec_from_file_location('authenticated_signed_terminal_optimizer',path)
        engine = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(engine)
        for family in args.family or ('compact78','raw78'):
            for cap in args.caps:
                for variant in ('baseline','exchanged'):
                    equation = inputs[family][variant]
                    child, projection, metrics = engine.optimize(equation,max_support=cap)
                    need(projection['unconstrained_removed'] == [], 'all integer coordinates uniquely restored')
                    verified = engine.verify(equation,child,projection)
                    polynomial = engine.expand(child)
                    need(polynomial['terms'] == independent_expansion(child), 'independent complete quartic expansion')
                    if family == 'compact78' and variant == 'baseline' and cap in existing_names:
                        need(child['metrics'] == census[existing_names[cap]]['metrics'],
                             'unchanged accepted compact profile is reproduced exactly')
                    record = dict(family=family,variant=variant,support_cap=cap,
                        input_sha256=digest(encoded(equation)), output_sha256=digest(encoded(child)),
                        projection_sha256=digest(encoded(projection)),
                        expanded_polynomial_sha256=digest(encoded(polynomial)),
                        metrics=child['metrics'], optimizer_metrics=metrics,
                        projection_verification=verified,
                        independent_entire_quartic_expansion='PASS',
                        unconstrained_removed=[],
                        restoration_support_histogram=dict(sorted(Counter(len(s['restoration']) for s in projection['steps']).items())),
                        largest_restoration_coefficient=max((abs(c) for s in projection['steps'] for c,m in s['restoration']),default=0))
                    records.append(record)
                    print(json.dumps(dict(family=family,variant=variant,cap=cap,
                        variables=child['metrics']['variables'],rows=child['metrics']['quadratic_rows'],
                        terms=child['metrics']['expanded_monomials'],height=child['metrics']['max_abs_expanded_coefficient'])),flush=True)
    for name,value in pins.items():
        need(digest((ROOT/name).read_bytes()) == value, 'frozen source unchanged after profile '+name)
    comparisons = []
    for family in args.family or ('compact78','raw78'):
        for cap in args.caps:
            pair = {r['variant']:r['metrics'] for r in records if r['family']==family and r['support_cap']==cap}
            a,b = pair['baseline'],pair['exchanged']
            comparisons.append(dict(family=family,support_cap=cap,
                exchanged_minus_baseline={k:b[k]-a[k] for k in ('variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient','max_abs_row_coefficient')}))
    result = dict(schema='bootstrap_guard_exchange_paired_coefficient_profile_v1',status='PASS',
        optimized_python=bool(sys.flags.optimize),source_pins=pins,
        authenticated_archive=dict(path=ARCHIVE,sha256=ARCHIVE_HASH,member=MEMBER,member_sha256=MEMBER_HASH),
        guard_exchange=exchange,records=records,paired_comparisons=comparisons,
        source_builder_or_historical_emitter_executed=False,
        scope='Research-only paired optimizer profile. All complete integer projections verified and quartics independently expanded. No new accepted candidate, Lean proof, internal-ZFC derivation, or general guard-deletion claim.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('PROFILE PASS: '+str(args.output),flush=True)

if __name__ == '__main__':
    main()
