#!/usr/bin/env python3
"""Integrity and deterministic finite checks for this research delivery.

This is not an unbounded consistency test or a new proof-assistant endpoint.
The several-minute universal machine replay is an explicit optional command.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def run(command, log):
    with log.open('w') as stream:
        subprocess.run([str(x) for x in command], cwd=ROOT, check=True,
                       stdout=stream, stderr=subprocess.STDOUT)

def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def integrity():
    count = 0
    manifest = ROOT/'SHA256SUMS'
    if not manifest.exists():
        return {'status':'NOT_YET_WRITTEN_DURING_ASSEMBLY'}
    for line in manifest.read_text().splitlines():
        digest, relative = line.split('  ', 1)
        p = ROOT/relative
        assert p.is_file(), relative
        assert hashlib.sha256(p.read_bytes()).hexdigest() == digest, relative
        count += 1
    return {'status':'PASS', 'files':count}

def main():
    if not __debug__:
        raise SystemExit('Assertions are required; do not use python -O.')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path)
    p.add_argument('--whole-frame', action='store_true')
    p.add_argument('--codecs', action='store_true',
                   help='reoptimize every declared dictionary subset, including prior controls')
    a = p.parse_args()
    output = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-delivery-check-'))
    output.mkdir(parents=True, exist_ok=True)
    result = {'integrity':integrity()}

    run([sys.executable, '-B', ROOT/'formalism/raw_profiles.py',
         '--output', output/'theories', '--stage', '1'], output/'theories.log')
    actual = json.loads((output/'theories/results.json').read_text())
    expected = json.loads((ROOT/'formalism/results/results.json').read_text())
    assert actual == expected
    stage = json.loads((output/'theories/requested-stage.json').read_text())
    assert stage == {'bound':1, 'clauses':177, 'atoms':154, 'verdict':'SAT'}
    result['theories'] = {'status':'PASS', 'variants':len(actual['variants']), 'stage1':stage}

    # Decode every retained new best dictionary from its actual bit stream.
    sys.path.insert(0, str(ROOT/'formalism'))
    import raw_profiles as raw
    import encoding_experiments as enc
    targets = [(False,False,False),(False,True,False),(True,False,False),
               (True,True,False),(False,False,True)]
    decoded = []
    for ext, fused, member in targets:
        name = raw.variant_name(ext, fused, False, member)
        rows = raw.clauses(ext, fused, False, member)
        codec = enc.Codec(rows, 4, raw.CONSTANTS, raw.signature(fused or member))
        bits = (ROOT/'formalism/encoding_results'/(name+'.shared.bits')).read_text().strip()
        assert codec.decode(bits) == raw.canonical(rows)
        packed = (ROOT/'formalism/encoding_results'/(name+'.shared.bin')).read_bytes()
        padding = (-len(bits)) % 8
        packed_bits = ''.join(format(byte, '08b') for byte in packed)
        assert packed_bits == bits + '0' * padding
        decoded.append({'name':name, 'bits':len(bits), 'packed_bytes':len(packed),
                        'padding_bits':padding})
    result['static_dictionary_decodes'] = decoded
    if a.codecs:
        run([sys.executable, '-B', ROOT/'formalism/encoding_experiments.py',
             '--output', output/'codecs'], output/'codecs.log')
        assert json.loads((output/'codecs/results.json').read_text()) == json.loads(
            (ROOT/'formalism/encoding_results/results.json').read_text())
        result['dictionary_subset_optimization'] = 'PASS'

    run([sys.executable, '-B', ROOT/'grammar/verify.py', '--output', output/'grammar'],
        output/'grammar.log')
    result['grammar'] = json.loads((output/'grammar/verification.json').read_text())

    # Run the row checker on a temporary copy; its historical CLI writes beside itself.
    import shutil
    rowcheck = output/'check_increment_orientation_rows.py'
    shutil.copy2(ROOT/'runtime/check_increment_orientation_rows.py', rowcheck)
    run([sys.executable, '-B', rowcheck, ROOT/'runtime/reference/machine/zfc245_old.tm'],
        output/'orientation.log')
    result['increment_row_premises'] = json.loads((output/'increment-orientation-row-check.json').read_text())['status']

    run([sys.executable, '-B', ROOT/'contextual18/audit_contextual18.py',
         ROOT/'contextual18/candidate.json', '--runtime', ROOT/'grammar/runtime',
         '--output', output/'contextual18.json'], output/'contextual18.log')
    result['contextual18_grammar'] = json.loads((output/'contextual18.json').read_text())['status']
    state18 = output/'check_state18_context.py'
    shutil.copy2(ROOT/'state18_contract/check_state18_context.py', state18)
    run([sys.executable, '-B', state18, ROOT/'runtime/reference/machine/zfc245_old.tm'],
        output/'state18.log')
    result['state18_local_premises'] = 'PASS'

    preparation = load(ROOT/'source_search/prepare.py', 'source_preparation')
    package = preparation.extract(output/'source-reference')
    for script, target in [('generate_combined.py','combined_variants.json'),
                           ('generate_parameter_targets.py','genc_parameter_variants.json')]:
        run([sys.executable, '-B', ROOT/'source_search'/script, '--package', package,
             '--output', output/target], output/(script+'.log'))
        assert json.loads((output/target).read_text()) == json.loads((ROOT/'source_search'/target).read_text())
    result['symbolic_source_target_families'] = {'status':'PASS', 'counts':[96,96]}

    if a.whole_frame:
        run([sys.executable, '-B', ROOT/'grammar/verify.py', '--whole-frame',
             '--output', output/'whole-frame'], output/'whole-frame.log')
        result['whole_frame'] = 'PASS'
    result['status'] = 'PASS_REQUESTED_FINITE_AND_SYMBOLIC_CHECKS'
    result['scope'] = 'No new binary machine below245, no unbounded consistency verdict, no proof-assistant endpoint.'
    (output/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'], 'output':str(output),
                      'theories':len(actual['variants']), 'static_decodes':decoded},indent=2))

if __name__ == '__main__':
    main()
