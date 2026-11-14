#!/usr/bin/env python3
"""Reproduce the accepted PA194N checks without network or search.

Default: integrity, input bindings, command identities, exact graph novelty,
construction with all source contracts, and independent literal-tape replay.
--quick omits the two full symbolic physical replays. Neither mode claims
an end-to-end proof-assistant theorem of the inherited PA calibration.
"""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(claim, message):
    if not claim:
        raise RuntimeError(message)

def run(script, *args):
    print('Checking', script.relative_to(ROOT) if script.is_relative_to(ROOT) else script.name, flush=True)
    subprocess.run([sys.executable, '-B', str(script), *map(str, args)], check=True)

def main():
    require(__debug__ and not sys.flags.optimize, 'Use Python without -O or PYTHONOPTIMIZE.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true', help='Omit full symbolic physical replays.')
    ap.add_argument('--work', type=Path, help='Nonexistent output directory; default is a fresh temporary directory.')
    args = ap.parse_args()
    if args.work:
        work = args.work.resolve()
        require(not work.exists(), '--work must name a nonexistent directory.')
        work.mkdir(parents=True)
    else:
        work = Path(tempfile.mkdtemp(prefix='pa194N-verify-'))
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for name, expected in manifest['sha256'].items():
        p = ROOT / name
        require(p.is_file() and digest(p) == expected, 'Integrity mismatch: ' + name)
    print('Integrity passed for', len(manifest['sha256']), 'files.', flush=True)

    construction = ROOT / 'construction'
    independent = ROOT / 'verification/independent'
    require(digest(construction/'machine/pa194N.tm') == digest(independent/'dense.tm'), 'Dense input mismatch.')
    require(digest(construction/'machine/pa194N.native.tm') == digest(independent/'native.tm'), 'Native input mismatch.')
    source = json.loads((independent/'source.json').read_text())
    sites = [[''.join(map(str,p)),op,arg] for p,op,arg in source['sites']]
    require(sites == json.loads((construction/'machine/sites.json').read_text()), 'Source-site mismatch.')
    require(source['instructions'] == json.loads((construction/'machine/instructions.json').read_text()), 'Source graph mismatch.')
    for name, expected in json.loads((construction/'PROVENANCE.json').read_text())['inputs'].items():
        require(digest(construction/name) == expected, 'Pinned construction input mismatch: ' + name)
    for folder, prefix in [('literal_inputs',''),('reference_hashes','reference/')]:
        for name, expected in json.loads((independent/'PROVENANCE.json').read_text())[folder].items():
            require(digest(independent/(prefix+name)) == expected, 'Independent input mismatch: ' + name)

    copied = work/'construction'
    shutil.copytree(construction, copied, ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
    run(copied/'mathematics/check_emitter_and_words.py')
    run(ROOT/'comparison/check_nopush_novelty.py', '--output', work/'novelty.json')
    if not args.quick:
        run(copied/'build_nopush.py')
        require(digest(copied/'machine/pa194N.tm') == digest(construction/'machine/pa194N.tm'), 'Rebuilt table changed.')
        require(json.loads((copied/'machine/construction_receipt.json').read_text()) ==
                json.loads((construction/'machine/construction_receipt.json').read_text()), 'Construction receipt changed.')
        run(independent/'check.py', '--output', work/'independent')
        for name in ['contracts.json','list_lemmas.json','blank_seed.json','receipt.json']:
            require(digest(work/'independent'/name) == digest(independent/'output'/name), 'Independent result changed: ' + name)
    result = {'status':'PASS','mode':'quick' if args.quick else 'full',
              'working_states':194,'dense_sha256':digest(construction/'machine/pa194N.tm'),
              'physical_replays_performed':not args.quick,'kernel_checked':False,
              'scope':'Integrity, command identities, graph novelty, and (unless quick) both complete physical replays. Inherited logical calibration is an ordinary mathematical dependency.'}
    (work/'verification_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    print('Reproduction output:',work)

if __name__ == '__main__':
    main()
