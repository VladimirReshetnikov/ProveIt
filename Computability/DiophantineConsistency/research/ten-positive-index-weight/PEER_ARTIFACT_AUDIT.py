#!/usr/bin/env python3
"""Exercise the reviewed checker on complete private artifact corruptions.

This supplements the independent ordinary and degree review. It imports only
the exact pinned checker, runs no producer or incoming code, and writes no
candidate or parent artifact. Every mutation starts from a fresh byte copy.
"""
import argparse
from contextlib import redirect_stdout
import gzip
from hashlib import sha256
import importlib.util
import io
import json
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
    'PROOF.md': '686ad651212a034b003b565bd3d337f11f3b4596e3576224a735c4dd263a8350',
    'README.md': '41be75c3ee8ce27ea88646368dd62253a3c74572f4352aef8f4bfd32681ed0a3',
    'SOURCE_PINS.json': 'babee254595e3800fa46a121b0307038dd429b360906bd3cd76a044b686dcf93',
    'build.py': '04978e6c2f4ceb131c4b6c607b1ca20a8cc3a4875c471de2f1f39548861646ac',
    'check.py': '189e12230d216a0e2e56537aca9d941a1a178db6e138b11dbcd49d9b7711c930',
    'zero98.json': 'bd7ae70e69288cb035f24a564f99e9ea4282b5f647558e52ad34170f73795f82',
    'direct103.json': '42e3cfdb31d3ca792b3956085104ebcefd84490df6a51e7b424cdf76651c4439',
    'zero98_CUTS.json': 'f78eb1c26f9e246b2ede55a67319a321f67b306fc4d727a6791104fafef98605',
    'direct103_CUTS.json': '14faf1a782ba715b501e9385aef1147ca03f5ecdda56edf501eedf5b3a5cdfbf',
}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def digest(data):
    return sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    for name, pin in PINS.items():
        need(digest((HERE / name).read_bytes()) == pin, 'reviewed complete member ' + name)
    names = list(PINS) + ['parents/' + n for n in ['PROOF.md', 'MANIFEST.json', 'zero98.json', 'direct103.json']]
    names += ['coefficients/' + n for n in ['BINDING.json', 'beta.bin.gz', 'K.bin.gz', 'MC.bin.gz', 'MF_source.bin.gz']]
    payload = {n: (HERE / n).read_bytes() for n in names}
    spec = importlib.util.spec_from_file_location('reviewed_index_weight_checker_for_peer_controls', HERE / 'check.py')
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    need(not any('terminal_elimination' in n or 'monic_engine' in n for n in sys.modules), 'no optimizer imported')
    rejected = []
    with tempfile.TemporaryDirectory(prefix='index-weight-peer-artifacts-') as directory:
        base = Path(directory)
        folder = base / 'packet'
        output = base / 'receipt.json'
        checker.HERE = folder
        checker.ROOT = ROOT

        def reset(sealed=False):
            if folder.exists():
                for p in sorted(folder.rglob('*'), key=lambda p: len(p.parts), reverse=True):
                    p.unlink() if p.is_file() else p.rmdir()
            folder.mkdir(exist_ok=True)
            for name, data in payload.items():
                target = folder / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            if sealed:
                (folder / 'MANIFEST.json').write_text(json.dumps({'files': {n: digest(b) for n, b in payload.items()}}, sort_keys=True) + '\n')
            if output.exists():
                output.unlink()

        def replay():
            previous = sys.argv
            sys.argv = ['reviewed-check.py', '--output', str(output)]
            try:
                with redirect_stdout(io.StringIO()):
                    checker.main()
            finally:
                sys.argv = previous

        def edit(name, action):
            p = folder / name
            data = json.loads(p.read_bytes())
            action(data)
            p.write_text(json.dumps(data, sort_keys=True) + '\n')

        def row(data, name):
            return next(r for r in data['source'] if r[0] == name)

        def reject(name, mutation, sealed=False):
            reset(sealed)
            mutation()
            try:
                replay()
            except (ValueError, KeyError, TypeError, IndexError, OSError, EOFError) as error:
                rejected.append({'name': name, 'exception': type(error).__name__, 'reason': str(error)})
            else:
                raise ValueError('actual checker accepted mutated artifact: ' + name)

        reset()
        replay()
        need(json.loads(output.read_bytes())['status'] == 'PASS', 'unsealed positive control')
        reset(True)
        replay()
        need(json.loads(output.read_bytes())['status'] == 'PASS', 'closed positive control includes nested parent manifest')
        for candidate, exact in [('zero98.json', 360), ('direct103.json', 332)]:
            prefix = candidate + ': '
            reject(prefix + 'restore old H multiplier', lambda n=candidate: edit(n, lambda d: row(d, 'kI').__setitem__(2, 'Hp')))
            reject(prefix + 'wrong L operand', lambda n=candidate: edit(n, lambda d: row(d, 'L').__setitem__(3, 'R')))
            reject(prefix + 'alter unrelated main base', lambda n=candidate: edit(n, lambda d: row(d, 'Am1').__setitem__(3, 'X')))
            reject(prefix + 'alter complete norm coefficient', lambda n=candidate: edit(n, lambda d: row(d, '64scaXb').__setitem__(2, 63)))
            reject(prefix + 'change positive domain', lambda n=candidate: edit(n, lambda d: d.update(domain='unrestricted integers')))
            reject(prefix + 'change fixed port order', lambda n=candidate: edit(n, lambda d: d['fixed_numerals'].reverse()))
            reject(prefix + 'wrong exact degree', lambda n=candidate, e=exact: edit(n, lambda d: d.update(exact_degree=e - 8)))
            reject(prefix + 'wrong propagated L degree', lambda n=candidate: edit(n, lambda d: d['register_degrees'].update(L=10)))
            cuts = candidate.replace('.json', '_CUTS.json')
            reject(prefix + 'omit retained row map', lambda n=cuts: edit(n, lambda d: d['retained_rows'].pop()))
            reject(prefix + 'wrong parent hash', lambda n=cuts: edit(n, lambda d: d.update(parent_sha256='0' * 64)))
        reject('direct: omit q4 correction before divisibility', lambda: edit('direct103.json', lambda d: row(d, 'inner').__setitem__(3, 0)))
        reject('coherent coefficient binding changed', lambda: edit('coefficients/BINDING.json', lambda d: d['ports']['K0'].update(bits=1)))
        reject('whole compressed fixed numeral changed', lambda: (folder / 'coefficients/K.bin.gz').write_bytes(gzip.compress(gzip.decompress(payload['coefficients/K.bin.gz']) + b'\x00', mtime=0)))
        reject('copied accepted parent changed', lambda: edit('parents/zero98.json', lambda d: d.update(exact_degree=360)))
        reject('closed inventory drops nested parent manifest', lambda: edit('MANIFEST.json', lambda d: d['files'].pop('parents/MANIFEST.json')), True)
        reject('unlisted payload is rejected', lambda: (folder / 'unlisted.json').write_text('{}\n'), True)
        reject('nested parent manifest bytes are authenticated', lambda: (folder / 'parents/MANIFEST.json').write_text('{}\n'), True)

    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize), reviewed_files=PINS,
                  positive_controls=['complete unsealed packet', 'complete closed packet including parents/MANIFEST.json'],
                  rejected_actual_artifacts=rejected, rejected_count=len(rejected),
                  checker_imported=True, builder_or_optimizer_or_incoming_code_executed=False,
                  immutable_inputs_modified=False, unbounded_proof_replaced_by_controls=False,
                  audit_sha256=digest(Path(__file__).read_bytes()))
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output.exists():
        need(args.output.read_text() == text, 'refuse changed peer receipt overwrite')
    else:
        args.output.write_text(text)
    print(json.dumps({'status': 'PASS', 'rejected_actual_artifacts': len(rejected), 'positive_controls': 2}, sort_keys=True))


if __name__ == '__main__':
    main()
