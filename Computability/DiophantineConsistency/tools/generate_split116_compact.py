#!/usr/bin/env python3
"""Reproduce coherent split116 candidate instances from pinned arrival ZIPs.

No delivered tree is changed. The retained upstream programs are authenticated
before adaptation. Finite replay does not establish an unbounded compiler or
an object-language ZFC consistency theorem.
"""
from pathlib import Path
from functools import lru_cache
import argparse
import gzip
import hashlib
import io
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
ARRIVAL = '7331974b69'
LEGACY_COMMIT = '4edbd53636'
LEGACY_SHA256 = 'd4ebd34d36becdc5142526ccf02f6e2c239ac93c8528b39235ee798b1aa10da1'
ARCHIVES = {
    54: ('con-zfc-calibrated-carry-4b4349064a.zip',
         'e8045da2c6a33b84a51cfb7fa543fb5ccd1db857d283af5094a89f09ec6be2be'),
    55: ('con_zfc_congruence_norms_2026-10-23.zip',
         '83e9ff8c09deb57a93fcd8a7094f2d4a37f17618ad26a7ff7a403ca6aaea942e'),
    57: ('ConZFC_Separated_Degrees_2026-10-23.zip',
         'd495c1e4121d16117b14b7f298780702a638c373a2609f23a90f904ba08aef02'),
    59: ('ZFC_Diophantine_Degree_Separated_2026-10-23.zip',
         '68e5cf243341e41ba0555a53eb1110fa987babb3194241b9c005ddd7aba9d702'),
}
VARIANTS = {
    'compact57': {'package': 57, 'bits': [590069, 592884, 590069, 590070],
                  'height': 1182955, 'kappa': 1182967},
    'compact54': {'package': 54, 'bits': [429959, 434054, 429959, 429960],
                  'height': 864015, 'kappa': 864027},
    'compact54-sharp': {'package': 54, 'bits': [429959, 434054, 429959, 429960],
                        'height': 864014, 'kappa': 864026},
}
ALIASES = {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'}
SCRIPTS = ['build_nine.py', 'circuit.py', 'verify_nine.py',
           'independent_review.py', 'check_source_independent.py']


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n')


@lru_cache(None)
def archive(package):
    name, expected = ARCHIVES[package]
    raw = subprocess.run(['git', 'show', f'{ARRIVAL}:docs/incoming/{name}'],
                         cwd=REPO, check=True, capture_output=True).stdout
    require(sha(raw) == expected, f'archive hash {package}')
    z = zipfile.ZipFile(io.BytesIO(raw))
    names = [n for n in z.namelist() if not n.endswith('/')]
    prefix = names[0].split('/')[0] + '/'
    require(all(n.startswith(prefix) for n in names), 'one archive root')
    return z, prefix


def member(package, name):
    z, prefix = archive(package)
    return z.read(prefix + name)


def rewrite(text, old, new, count=1):
    require(text.count(old) == count, f'adaptation occurrence count: {old[:80]!r}')
    return text.replace(old, new)


def generate_legacy(variant, destination):
    """Replay the actual checkpoint generator, preserving its old provenance.

    A new generator hash must not silently reseal the two frozen instances.
    The old program is retained verbatim in scratch and its repository roots
    are explicitly supplied, so its original source hash remains truthful.
    """
    source = subprocess.run(['git', 'show', f'{LEGACY_COMMIT}:' +
        'Computability/DiophantineConsistency/tools/generate_split116_compact.py'],
        cwd=REPO, check=True, capture_output=True).stdout
    require(sha(source) == LEGACY_SHA256, 'legacy generator identity')
    with tempfile.TemporaryDirectory(prefix='proveit-split116-legacy-') as td:
        path = Path(td)/'research/tools/generate_split116_compact.py'
        path.parent.mkdir(parents=True)
        path.write_bytes(source)
        namespace = {'__name__': 'split116_checkpoint_generator', '__file__': str(path)}
        exec(compile(source, str(path), 'exec'), namespace)
        namespace['ROOT'], namespace['REPO'] = ROOT, REPO
        namespace['generate'](variant, destination)


def materialize(destination, config, ports):
    bodies = [json.loads(p.read_text()) for p in sorted((destination/'generated').glob('split_116_*.json'))
              if not p.name.endswith('_degree.json')]
    fixed_names = {n['name'] for body in bodies for n in body['nodes'] if n['kind'] == 'fixed'}
    body = bodies[0]
    values = {'base_scale': 1 << config['kappa'],
              'threshold_scale': 1 << config['threshold_scale_exponent']}
    for r in body['coefficient_recipes']:
        values[r['name']] = sum(t['coefficient'] * math.prod(ports[p]**e for p, e in
            zip(('beta', 'K0', 'MC', 'MF'), t['powers'])) for t in r['terms'])
    records = []
    for name in sorted(fixed_names):
        value = values[name]
        raw = abs(value).to_bytes(max(1, (abs(value).bit_length()+7)//8), 'little')
        blob = gzip.compress(raw, mtime=0)
        # The OS byte varies across Python versions. Canonicalize generated
        # payloads only; received whole-tuple payloads are retained verbatim.
        blob = blob[:9] + b'\xff' + blob[10:]
        path = destination/'fixed'/f'{name}.bin.gz'
        path.parent.mkdir(exist_ok=True)
        path.write_bytes(blob)
        records.append({'name': name, 'sign': (value > 0)-(value < 0),
                        'bits': abs(value).bit_length(), 'bytes': len(raw),
                        'path': f'fixed/{name}.bin.gz', 'sha256': sha(raw),
                        'gzip_sha256': sha(blob)})
    write_json(destination/'fixed/BINDING.json', {
        'schema': 'signed-little-endian-materialized-fixed-leaves-v1',
        'variant': config['variant'], 'endianness': 'little',
        'tuple_binding': 'coefficients/compact_tuple/COEFFICIENT_BINDING.json',
        'base_scale_exponent': config['kappa'],
        'threshold_scale_exponent': config['threshold_scale_exponent'],
        'live_fixed_leaves': records, 'total_raw_bytes': sum(r['bytes'] for r in records),
        'total_gzip_bytes': sum((destination/r['path']).stat().st_size for r in records)})


def extra_checks(destination, config, ports):
    kernels = json.loads((destination/'data/split_kernels.json').read_text())
    bounds = []
    actuals = []
    factorized = []
    for kernel in kernels['kernels']:
        for term in kernel['terms']:
            bound = sum(abs(t['coefficient']) * (1 << sum(e*b for e, b in
                zip(t['powers'], config['bits']))) for t in term['coefficient'])
            polynomial = {tuple(t['powers']): t['coefficient'] for t in term['coefficient']}
            if config['variant'] == 'compact54-sharp' and polynomial == {
                    (1, 0, 0, 0): 2, (1, 1, 0, 0): 2}:
                original_bits = bound.bit_length()
                bound = 2 * ((1 << config['bits'][0]) - 1) * (1 << config['bits'][1])
                factorized.append({'degree': kernel['degree'], 'exponent': term['exponent'],
                    'recipe': '2*beta+2*beta*K0 = 2*beta*(K0+1)',
                    'old_termwise_majorant_bits': original_bits,
                    'factorized_majorant_bits': bound.bit_length()})
            actual = sum(t['coefficient'] * math.prod(ports[p]**e for p, e in
                zip(('beta', 'K0', 'MC', 'MF'), t['powers'])) for t in term['coefficient'])
            require(abs(actual) < 1 << config['height'], 'actual weighted coefficient height')
            bounds.append(bound)
            actuals.append((abs(actual), kernel['degree'], term['exponent']))
    require(len(bounds) == 89 and max(bounds).bit_length() == config['height'], 'all89 majorants')
    if config['variant'] == 'compact54-sharp':
        require(len(factorized) == 1 and factorized[0]['degree'] == 1 and
                factorized[0]['exponent'] == 383, 'unique factorized transport record')
        maximum = max(actuals)
        require(maximum[0].bit_length() == config['height'], 'smallest dyadic kernel height')
        write_json(destination/'HEIGHT_CERTIFICATE.json', {
            'status': 'PASS', 'weighted_records': 89, 'unchanged_termwise_records': 88,
            'factorized_records': factorized,
            'generic_assumptions': ['beta,K0 are integers',
                '0<=beta<2^429959', '0<=K0<2^434054'],
            'factorized_bound': '|2*beta+2*beta*K0| <= 2*(2^429959-1)*2^434054 < 2^864014',
            'reason': 'K0+1<=2^434054; beta<=2^429959-1; all factors nonnegative.',
            'maximum_actual_absolute_coefficient_bits': maximum[0].bit_length(),
            'maximum_actual_at_degree': maximum[1], 'maximum_actual_at_exponent': maximum[2],
            'minimal_dyadic_height_for_fixed_kernel': True,
            'kappa_parity': 'No parity premise: 2418 is even, L=b*B^2279, c=2^(8*kappa-11).',
            'scope': 'Exact literal kernel-height certificate; no native calibration or consistency theorem.'})
    cases = []
    for k in range(32):
        nu = config['kappa'] + 2*k
        mask_population = 139*nu - 31*k - 22
        log_L = k + 2279*nu
        log_N = config['threshold_scale_exponent'] + k + 1201*nu
        require(2*log_N == log_L + mask_population, 'exact decoder threshold')
        cases.append({'log2_b': k, 'log2_B': nu, 'log2_L': log_L,
                      'popcount_T': mask_population, 'log2_N': log_N})
    led = json.loads((destination/'generated/LEDGER.json').read_text())['split_116']
    natural = json.loads((destination/'generated/split_116_natural.json').read_text())
    require(led['positive_operations'] == 473 and led['exact_degree'] == 1910404,
            'selected candidate metrics')
    require(natural['total_operations'] == 480, 'natural coordinate operation ledger')
    require(led['base_scale_exponent'] == config['kappa'] and
            led['threshold_scale_exponent'] == config['threshold_scale_exponent'] and
            led['threshold_B_power'] == 1201, 'selected scales')
    binding = json.loads((destination/'fixed/BINDING.json').read_text())
    primary = json.loads((destination/'generated/split_116_positive.json').read_text())
    expected = {'base_scale': 1 << config['kappa'],
                'threshold_scale': 1 << config['threshold_scale_exponent']}
    for recipe in primary['coefficient_recipes']:
        expected[recipe['name']] = sum(t['coefficient'] * math.prod(ports[p]**e for p, e in
            zip(('beta', 'K0', 'MC', 'MF'), t['powers'])) for t in recipe['terms'])
    live = {n['name'] for n in primary['nodes'] if n['kind'] == 'fixed'}
    require(live == {r['name'] for r in binding['live_fixed_leaves']}, 'every live fixed leaf')
    for r in binding['live_fixed_leaves']:
        blob = (destination/r['path']).read_bytes()
        raw = gzip.decompress(blob)
        require(sha(blob) == r['gzip_sha256'] and sha(raw) == r['sha256'], 'fixed leaf bytes')
        value = r['sign'] * int.from_bytes(raw, 'little')
        require(value == expected[r['name']] and abs(value).bit_length() == r['bits'],
                'materialized fixed leaf denotes its exact whole-tuple recipe')
    result = {'status': 'PASS', 'variant': config['variant'],
              'weighted_coefficients_checked': 89, 'actual_weighted_coefficients_lt_height': True,
              'maximum_termwise_majorant_bit_length': max(bounds).bit_length(),
              'kappa': config['kappa'], 'threshold_scale_exponent': config['threshold_scale_exponent'],
              'threshold_scale_formula': '8*kappa-11', 'exact_threshold_cases': cases,
              'positive_operations': 473, 'exact_degree': 1910404,
              'natural_operations': 480, 'fixed_leaves_materialized': len(binding['live_fixed_leaves']),
              'scope': 'Finite actual-tuple/certificate/threshold checks; no unbounded calibration or Lean endpoint.'}
    write_json(destination/'EXTRA_CHECKS.json', result)


def generate(variant, destination):
    if variant in ('compact57', 'compact54'):
        return generate_legacy(variant, destination)
    spec = VARIANTS[variant]
    config = dict(spec, variant=variant, threshold_scale_exponent=8*spec['kappa']-11)
    require(not destination.exists(), f'destination exists: {destination}')
    destination.mkdir(parents=True)
    imported = []

    def retain(package, source, target):
        raw = member(package, source)
        path = destination/target
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
        imported.append({'path': target, 'sha256': sha(raw), 'package': package,
                         'archive': ARCHIVES[package][0], 'member': source})
        return raw

    for name in SCRIPTS:
        retain(59, 'nine_free_adjunct/'+name, 'provenance/upstream59/'+name)
    for name in ('source_system60.json', 'parent_source.json', 'split_code.json', 'split_kernels.json'):
        retain(59, 'nine_free_adjunct/data/'+name, 'data/'+name)
    retain(59, 'nine_free_adjunct/PROOF.md', 'provenance/59-free-coordinate-proof.md')
    retain(59, 'encoding/SPLIT_SOURCE_PROOF.md', 'provenance/59-source-proof.md')
    retain(59, 'nine_free_adjunct/LICENSE', 'provenance/LICENSE.59')
    retain(59, 'nine_free_adjunct/NOTICE.md', 'provenance/NOTICE.59.md')
    retain(55, 'native/SOURCE31_ADAPTER.md', 'provenance/SOURCE31_ADAPTER.md')
    package = spec['package']
    if package == 57:
        original = retain(57, 'coefficients/COEFFICIENT_BINDING.json', 'provenance/original_binding.json')
        retain(57, 'coefficients/PROOF.md', 'provenance/interface_proof.md')
        retain(57, 'coefficients/NOTICE.md', 'provenance/NOTICE.tuple.md')
        rows = json.loads(original)['materialization']['files']
        records = [(r['port'], 'coefficients/'+r['file'], r['bits'], r['raw_bytes'],
                    r['sha256'], r['gzip_sha256']) for r in rows]
        license_prefix = 'coefficients/licenses/'
    else:
        original = retain(54, 'native/COEFFICIENT_BINDING.json', 'provenance/original_binding.json')
        retain(54, 'native/INHERITED_SEPARATED_PROOF.md', 'provenance/interface_proof.md')
        retain(54, 'NOTICE.md', 'provenance/NOTICE.tuple.md')
        records = [(r['name'], 'native/'+r['name']+'.bin.gz', r['bits'], r['bytes'],
                    r['sha256'], r['gzip_sha256']) for r in json.loads(original)['ports']]
        license_prefix = 'native/licenses/'
    z, prefix = archive(package)
    for name in z.namelist():
        relative = name[len(prefix):]
        if relative.startswith(license_prefix) and not name.endswith('/'):
            retain(package, relative, 'provenance/licenses/'+relative[len(license_prefix):])
    payloads = []
    native_ports = {}
    for name, source, bits, length, raw_hash, gzip_hash in records:
        blob = retain(package, source, 'coefficients/compact_tuple/'+name+'.bin.gz')
        raw = gzip.decompress(blob)
        require(sha(blob) == gzip_hash and sha(raw) == raw_hash and len(raw) == length,
                'whole tuple payload identity')
        value = int.from_bytes(raw, 'little')
        require(value.bit_length() == bits, 'whole tuple bit length')
        native_ports[name] = value
        payloads.append({'name': name, 'path': name+'.bin.gz', 'bit_length': bits,
                         'bytes': length, 'sha256': raw_hash, 'gzip_sha256': gzip_hash})
    ports = {p: native_ports[n] for p, n in ALIASES.items()}
    require([ports[p].bit_length() for p in ALIASES] == spec['bits'], 'coherent width tuple')
    proof = destination/'provenance/interface_proof.md'
    binding = {'schema': 'coherent-fixed-materialized-tuple-v1', 'variant': variant,
               'port_aliases': ALIASES, 'payloads': payloads,
               'MF_convention': 'MF_source is already shifted exactly once.',
               'tuple_rule': 'All four payloads come from one complete selected arrival tuple.',
               'source_binding_path': '../../provenance/original_binding.json',
               'source_binding_sha256': sha(original),
               'complete_interface_proof_path': '../../provenance/interface_proof.md',
               'complete_interface_proof_sha256': sha(proof.read_bytes()),
               'old_source_adapter': '../../provenance/SOURCE31_ADAPTER.md'}
    write_json(destination/'coefficients/compact_tuple/COEFFICIENT_BINDING.json', binding)
    # The legacy verifier's two input aliases point to the same coherent tuple.
    wrapper = {'port_aliases': ALIASES, 'ports': [dict(port=r['name'],
        gzip_file='compact_tuple/'+r['path'], bits=r['bit_length'], bytes=r['bytes'],
        sha256=r['sha256'], gzip_sha256=r['gzip_sha256']) for r in payloads]}
    write_json(destination/'coefficients/COEFFICIENT_BINDING.json', wrapper)
    adaptations = []
    for name in SCRIPTS:
        before = (destination/'provenance/upstream59'/name).read_text()
        text = before
        if name == 'build_nine.py':
            text = rewrite(text, 'bits=(1064921,1070004,1064921,1064922) if split else BITS',
                           f'bits={tuple(spec["bits"])} if split else BITS')
            text = rewrite(text, "'coherent_tuple':'old31' if split else 'native52'",
                           f"'coherent_tuple':'{variant}' if split else 'native52'")
            text = rewrite(text,
                "        bound=max(bound,bnd)\n        return coefs[name]",
                "        if poly == {(1,0,0,0):2,(1,1,0,0):2}:\n"
                "            # Integer box: beta<=Bcap-1 and K0+1<=Qcap.\n"
                "            bnd=2*((1<<bits[0])-1)*(1<<bits[1])\n"
                "        bound=max(bound,bnd)\n        return coefs[name]")
        if name in ('verify_nine.py', 'independent_review.py', 'check_source_independent.py'):
            require('old_tuple' in text, 'legacy tuple path')
            text = text.replace('old_tuple', 'compact_tuple')
        if name == 'verify_nine.py':
            text = rewrite(text, "payloads.append('old31/'+r['name'])",
                           f"payloads.append('{variant}/'+r['name'])")
        if name == 'check_source_independent.py':
            text = rewrite(text, '17079501', str(config['threshold_scale_exponent']))
            text = rewrite(text, '2134939', str(config['kappa']), count=2)
        (destination/name).write_text(text)
        adaptations.append({'path': name, 'upstream_sha256': sha(before.encode()),
                            'adapted_sha256': sha(text.encode()),
                            'changed': before != text})
    write_json(destination/'CONFIG.json', config)
    write_json(destination/'SOURCE_PINS.json', {'imported': imported})
    write_json(destination/'PROVENANCE.json', {'arrival': ARRIVAL,
        'generator_sha256': sha(Path(__file__).read_bytes()),
        'archives': {str(k): {'name': ARCHIVES[k][0], 'sha256': ARCHIVES[k][1]}
                     for k in (55, 59, package)},
        'adaptations': adaptations, 'tuple_port_count': 4,
        'scope': 'Literal candidate construction and finite replay; no new consistency equivalence is asserted.'})
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    env.pop('PYTHONOPTIMIZE', None)
    replays = []
    for script in ('build_nine.py', 'verify_nine.py', 'independent_review.py', 'check_source_independent.py'):
        run = subprocess.run([sys.executable, '-B', str(destination/script)],
                             cwd=destination, env=env, capture_output=True)
        log = destination/'receipts'/f'{script}.log'
        log.parent.mkdir(exist_ok=True)
        log.write_bytes(run.stdout + run.stderr)
        require(run.returncode == 0, f'{script} failed; see {log}')
        replays.append({'script': script, 'status': 'PASS', 'exit_code': run.returncode,
                        'output_sha256': sha(log.read_bytes())})
    materialize(destination, config, ports)
    extra_checks(destination, config, ports)
    write_json(destination/'REPLAY.json', {'status': 'PASS', 'replays': replays,
        'scope': 'Finite exact identities, literal-circuit, whole-tuple, degree and threshold checks.'})
    (destination/'README.md').write_text(
        f'# Split116 with the whole {variant} tuple\n\n'
        'This is a separate candidate artifact; delivered packages are unchanged.\n'
        'Its positive and natural coordinate orders are `b,g,h,s,w,C,i,j,n`.\n'
        'The positive polynomial has 473 binary operations and exact degree 1,910,404;\n'
        'the natural polynomial has 480 operations and the same degree.\n\n'
        f'All four coefficient ports come from package {package}. MF_source is already shifted.\n'
        f'The weighted coefficient bound is 2^{spec["height"]}, the radix floor is\n'
        f'2^{spec["kappa"]}, and the threshold scale is 2^{config["threshold_scale_exponent"]}.\n'
        'Every live nonliteral fixed leaf is materialized as a signed magnitude in fixed/.\n\n'
        'Reproduce from the repository with `python -B tools/generate_split116_compact.py '
        f'--tuple {variant} --check` (from the research root).\n'
        'PROVENANCE.json binds the whole tuple, retained source/proofs and adapted code.\n'
        'REPLAY.json and EXTRA_CHECKS.json report finite checks.\n\n'
        'No new unbounded compiler calibration, Lean consistency endpoint, internal ZFC\n'
        'derivation, or global simplicity minimum is claimed for this candidate.\n')
    files = {p.relative_to(destination).as_posix(): sha(p.read_bytes())
             for p in sorted(destination.rglob('*')) if p.is_file()}
    write_json(destination/'MANIFEST.json', files)
    print(json.dumps({'variant': variant, 'status': 'PASS', 'files': len(files),
                      'positive_operations': 473, 'degree': 1910404,
                      'kappa': spec['kappa'], 'threshold_exponent': config['threshold_scale_exponent']}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tuple', choices=list(VARIANTS), default='compact57')
    parser.add_argument('--all', action='store_true')
    parser.add_argument('--check', action='store_true', help='regenerate in scratch and compare every byte')
    args = parser.parse_args()
    for variant in (list(VARIANTS) if args.all else [args.tuple]):
        destination = ROOT/'candidates/split116-compact'/variant
        if args.check:
            with tempfile.TemporaryDirectory(prefix='proveit-split116-') as td:
                fresh = Path(td)/variant
                generate(variant, fresh)
                old = {p.relative_to(destination).as_posix(): p.read_bytes()
                       for p in destination.rglob('*') if p.is_file()}
                new = {p.relative_to(fresh).as_posix(): p.read_bytes()
                       for p in fresh.rglob('*') if p.is_file()}
                require(old == new, f'candidate bytes differ for {variant}: '
                        f'missing={set(new)-set(old)}, extra={set(old)-set(new)}, '
                        f'changed={[p for p in old.keys() & new.keys() if old[p] != new[p]]}')
                print(f'BYTE-IDENTICAL PASS: {variant}, {len(new)} files')
        else:
            generate(variant, destination)


if __name__ == '__main__':
    main()
