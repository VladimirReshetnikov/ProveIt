#!/usr/bin/env python3
"""Optimizer-free74 domains, modified prefix/frame, Z inverses and quartics."""
import argparse
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from review_synchronized_certificates import full_sos


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(data):
    return sha256(data).hexdigest()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name,path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def reject(name, action):
    try:
        action()
    except (ValueError,RuntimeError,KeyError,IndexError,TypeError):
        return name
    raise ValueError('corruption accepted '+name)


def source_interface(report):
    need(report['status'] == 'PASS' and report['source_predicates'] == 74,
         'pinned independent ordinary74 source peer')
    need(report['independent_polynomial_implementation'] is True and
         report['independent_original_row_identities'] == 94 and
         report['independent_ordered_sign_steps'] == 574 and
         report['independent_strict_constructor_steps'] == 430 and
         report['nonnegative_prefix_coordinates'] == 642 and
         report['omitted_prefix_coordinate'] == 59 and
         report['actual_frame_argument_count'] == 43 and report['frame_contains_raw59'] is False,
         'explicit modified642-prefix and actual43-frame before source calibration')
    need(report['interpreted_local_calls_before_index_guards'] == [1,5,6] and
         report['parity_only_call_before_index_guards'] == 2 and
         report['interpreted_calls_after_index_guards'] == list(range(10)) and
         report['source_builder_optimizer_or_emitter_executed'] is False and
         report['projected_equation_or_metrics_claimed'] is False and report['lean_run'] is False,
         'acyclic power use and exact ordinary source boundary')
    for name,expected in report['source_pins'].items():
        need(digest((ROOT/name).read_bytes()) == expected,'whole independent source peer pin '+name)
    return dict(status='PASS',source_predicates=74,modified_nonnegative_prefix_coordinates=642,
        ordered_sign_steps=574,strict_constructor_steps=430,actual_frame_arguments=43,
        raw59_in_frame=False,local_calls_before_index_guards=[1,5,6],
        first_ten_calls_only_after_guard_recovery=True,
        source_identity_count=94,ordinary_proof='research/encoded-index-sign/PROOF.md',
        full_parent_restoration_required_before_source_semantics=True)


def domain(eq,cert,family,old,oldcert,raw,body,initial):
    n,nr = oldcert['baseline_body_variables'],oldcert['baseline_body_rows']
    indices = oldcert['baseline_raw_indices']
    mp = {v:i for i,v in enumerate(indices)}
    variables = raw['variables'] if family == 'raw' else body['variables']
    rows = [dict(label=r['label'],terms=r['terms']) for r in raw['rows']] if family == 'raw' else body['residuals']
    need(old['variables'][:n] == variables and old['residuals'][:nr] == rows,
         'frozen75 body is original source with all metadata and coefficients')
    need(eq['domain'] == 'unrestricted integers' and eq['variables'][:n] == variables and
         eq['residuals'][:nr] == rows,'all original body records preserved verbatim')
    need(cert['baseline_body_variables'] == n and cert['baseline_body_rows'] == nr and
         cert['baseline_raw_indices'] == indices,'whole original body/raw-coordinate map')
    deleted = [i for i,g in enumerate(oldcert['guards']) if g['predicate']['kind'] == 'retained_scalar'
               and g['predicate']['raw_variables'] == [59]]
    need(len(oldcert['guards']) == 75 and len(deleted) == 1 and
         cert['removed_original_scalar_guard'] == 59 and cert['retained_parent_predicates'] == 74 and
         cert['inherited_parent_removed_original_scalar_guard'] == oldcert['removed_original_scalar_guard'] == 93
         and cert['deleted_parent_guard_index'] == deleted[0], 'delete precisely original scalar59 from75')
    selected = [(i,g) for i,g in enumerate(oldcert['guards']) if i not in deleted]
    predicates = [g['predicate'] for i,g in selected]
    scalar = {p['raw_variables'][0] for p in predicates if p['kind'] == 'retained_scalar'}
    need(len(scalar) == 71 and len(initial) == 61 and set(initial)-scalar == {59,93}
         and {94,95,113,537,694,825} <= scalar,
         'exact59 direct initial signs and all early/bootstrap/shifted-t premises retained')
    need([p for p in predicates if p['kind'] != 'retained_scalar'] == [
        dict(kind='strict_common_V',raw_variables=[656],terms=[[1,[mp[656]]],[-1,[]]]),
        dict(kind='paired_index_slacks',raw_variables=[674,861],terms=[[1,[mp[674],mp[861]]]]),
        dict(kind='factorial_lower_bound',raw_variables=[87],terms=[[1,[mp[87]]],[-2,[]]])],
        'unchanged strictV/product/f>=2 predicates, including exact coefficients')
    need(len(eq['variables']) == n+222 and len(eq['residuals']) == nr+74 and len(cert['guards']) == 74,
         'complete74-predicate dimensions with no extra defining wire')
    for j,(old_index,old_guard) in enumerate(selected):
        a,b,c = range(n+3*j,n+3*j+3)
        p = old_guard['predicate']
        need(cert['guards'][j] == dict(predicate=p,auxiliary=[a,b,c]),
             'every exact retained predicate and complete fresh triple')
        need(eq['variables'][a:c+1] == [old['variables'][v] for v in old_guard['auxiliary']],
             'all surviving auxiliary metadata preserved verbatim from75')
        need(eq['residuals'][nr+j] == dict(label=old['residuals'][nr+old_index]['label'],
             terms=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]),
             'every complete quadratic guard row and old label, with only private indices shifted')
    return dict(original_body_variables=n,original_body_rows=nr,predicates=74,
        retained_original_scalar_predicates=71,initial_direct_semantic_signs=59,
        modified_prefix_coordinates_after_independent_recovery=642,
        only_deleted_parent_scalar_guard=59,remaining_predicate_metadata_preserved=True,
        additional_defining_wires=0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    if (HERE/'MANIFEST.json').exists():
        seal = load(HERE/'MANIFEST.json')['files']
        need(set(seal) == {str(p.relative_to(HERE)) for p in HERE.rglob('*')
                          if p.is_file() and p.name != 'MANIFEST.json'},'closed full profile inventory')
        for name,expected in seal.items():
            need(digest((HERE/name).read_bytes()) == expected,'sealed profile member '+name)
    pins = load(HERE/'SOURCE_PINS.json')
    for name,expected in pins['files'].items():
        need(digest((ROOT/name).read_bytes()) == expected,'whole frozen input '+name)
    predecessor = ROOT/'research/factorial-radius-output-sign-profile'
    oldseal = load(predecessor/'MANIFEST.json')['files']
    need(set(oldseal) == {str(p.relative_to(predecessor)) for p in predecessor.rglob('*')
                         if p.is_file() and p.name != 'MANIFEST.json'},'closed frozen75 parent inventory')
    for name,expected in oldseal.items():
        need(digest((predecessor/name).read_bytes()) == expected,'complete frozen75 member '+name)
    build = load(HERE/'BUILD.json')
    need(digest((HERE/'build.py').read_bytes()) == build['generator_sha256'],'producer pin')
    for name,expected in build['files'].items():
        need(digest((HERE/name).read_bytes()) == expected,'whole generated equation/inverse/quartic '+name)
    # The pinned independent peer explicitly verifies the modified prefix and
    # exact frame, including weak-radix carry and the final moduli product.
    # Replay it in scratch before treating any source semantics as licensed.
    peer = ROOT/'reviews/encoded-index-sign-peer.py'
    reference = load(peer.with_name('encoded-index-sign-peer_OPTIMIZED.json' if sys.flags.optimize
                                     else 'encoded-index-sign-peer.json'))
    recovery = source_interface(reference)
    with tempfile.TemporaryDirectory(prefix='encoded74-source-peer-replay-') as tmp:
        output = Path(tmp)/'peer.json'
        command = [sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])
        proc = subprocess.run(command+[str(peer),'--output',str(output)],capture_output=True,text=True)
        need(proc.returncode == 0,'independent modified-prefix/frame scratch replay '+proc.stderr)
        need(load(output) == reference,'entire peer replay agrees with pinned independent source receipt')
    recovery['independent_peer_replayed_into_scratch'] = True
    recovery['independent_peer_receipt_sha256'] = digest(json.dumps(
        {k:v for k,v in reference.items() if k != 'optimized_python'},sort_keys=True).encode())
    mutations = []
    bad = deepcopy(reference)
    bad['frame_contains_raw59'] = True
    mutations.append(reject('silently use frame containing raw59',lambda:source_interface(bad)))
    bad = deepcopy(reference)
    bad['nonnegative_prefix_coordinates'] = 643
    mutations.append(reject('assume full prefix before encoded sign recovery',lambda:source_interface(bad)))
    raw = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    body = load(ROOT/'candidates/projected-radius-mixed-bounds/source/natural667.json')
    restore = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_restoration.json')
    prior = load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    primitive = module('pinned_independent_raw_compact_inverse',ROOT/'research/paired-index-guard-profile/check.py')
    fixtures = module('pinned_independent_signed_controls',ROOT/'candidates/projected-radius-integers/check.py')
    domains,parents = {},{}
    for family in ('compact','raw'):
        old,oldcert = load(predecessor/family/'parent.json'),load(predecessor/family/'domain.json')
        eq,cert = load(HERE/family/'parent.json'),load(HERE/family/'domain.json')
        parents[family] = eq
        initial = prior['prefix_proof']['initial_semantic_guard_indices']
        domains[family] = domain(eq,cert,family,old,oldcert,raw,body,initial)
        bad = deepcopy(eq)
        bad['residuals'][-1]['terms'][1][0] = -1
        mutations.append(reject('weaken actual f-2 predicate '+family,
            lambda:domain(bad,cert,family,old,oldcert,raw,body,initial)))
        bad = deepcopy(cert)
        bad['removed_original_scalar_guard'] = 94
        mutations.append(reject('delete direct remainder sign in place of59 '+family,
            lambda:domain(eq,bad,family,old,oldcert,raw,body,initial)))
        bad = deepcopy(eq)
        bad['variables'][-1]['name'] += '.changed'
        mutations.append(reject('alter surviving predicate auxiliary metadata '+family,
            lambda:domain(bad,cert,family,old,oldcert,raw,body,initial)))
        bad = deepcopy(eq)
        bad['residuals'][0]['terms'][0][0] += 1
        mutations.append(reject('change original body coefficient '+family,
            lambda:domain(bad,cert,family,old,oldcert,raw,body,initial)))
    bridge = primitive.raw_compact_bijection(parents['raw'],parents['compact'],restore,'direct',raw['rows'])
    need(bridge['unique_affine_restorations'] == bridge['forward_monic_uniqueness_rows'] == 592
         and bridge['sign_premises'] == 0,'all592 forward and reverse monic integer restorations')
    archive = REPO/pins['archive']
    need(digest(archive.read_bytes()) == pins['archive_sha256'],'whole independent arithmetic archive')
    census = load(HERE/'CENSUS.json')
    parent_census = load(predecessor/'CENSUS.json')
    need(len(census) == 17 and set(census) == set(parent_census),'same17 settings including raw8/16 default')
    for name,record in census.items():
        need((record['support_cap'],record['affine_cap']) ==
             (parent_census[name]['support_cap'],parent_census[name]['affine_cap']),
             'each support/affine configuration matches frozen75')
    results = {}
    with tempfile.TemporaryDirectory(prefix='encoded74-independent-projection-') as tmp,zipfile.ZipFile(archive) as z:
        for name,expected in pins['members'].items():
            need(digest(z.read(name)) == expected,'whole pinned arithmetic member '+name)
        for name in ('verify_projection.py','independent_polynomial.py','audit_common_radix.py'):
            member = next(m for m in pins['members'] if m.endswith('/'+name))
            (Path(tmp)/name).write_bytes(z.read(member))
        sys.path.insert(0,str(tmp))
        from verify_projection import verify
        for name,record in census.items():
            parent = parents[name.split('/')[0]]
            out = load(HERE/name/'equation.json')
            cert = load(HERE/name/'projection.json')
            quartic = load(HERE/name/'polynomial.json')
            need(cert['unconstrained_removed'] == [] and out['metrics'] == record['metrics'] and
                 len(cert['steps']) == record['unique_signed_restorations'],
                 'complete unique-coordinate inverse and freshly measured metric ledger')
            results[name] = dict(projection=verify(parent,out,cert),full_quartic=full_sos(out,quartic),
                arbitrary_signed_restoration_fixtures=fixtures.restoration_controls(parent,out,cert))
            if cert['steps']:
                bad = deepcopy(cert)
                bad['steps'][0]['restoration'][0][0] += 1
                mutations.append(reject('alter signed inverse '+name,lambda:verify(parent,out,bad)))
            bad = deepcopy(quartic)
            bad['terms'][0][0] += 1
            mutations.append(reject('alter complete quartic '+name,lambda:full_sos(out,bad)))
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),
        source_guard_recovery=recovery,literal_domains=domains,raw_compact_integer_bijection=bridge,
        profiles=results,rejected_corruptions=mutations,optimizer_imported=False,lean_run=False,
        source_pins={str(p.relative_to(ROOT)):digest(p.read_bytes()) for p in
                     (HERE/'README.md',HERE/'SOURCE_PINS.json',HERE/'BUILD.json',Path(__file__))},
        scope='Fresh complete74-predicate research systems; exact unrestricted integer inverses before source semantics; separately pinned and replayed642-prefix/43-frame ordinary proof; full quartics. No frontier promotion, optimum, native/internal-ZFC/Lean claim.')
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status='PASS',profiles=len(results),corruptions=len(mutations),
        raw_compact_bijection=bridge,modified_prefix_coordinates=642,actual_frame_arguments=43),indent=2))


if __name__ == '__main__':
    main()
