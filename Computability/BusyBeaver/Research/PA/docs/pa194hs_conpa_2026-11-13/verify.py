#!/usr/bin/env python3
"""Reproduce the delivered machines, certificates and exact novelty checks.

The default replays both construction symbolic verifiers. --full also
rederives independent literal-tape contracts from the actual transition rows.
The release is read-only: all regenerated evidence goes to a temporary copy.
Python 3.10+, standard library; assertions must remain enabled.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def need(condition, message):
    if not condition:
        raise RuntimeError(message)

def manifest_check():
    manifest = ROOT / 'SHA256SUMS'
    if not manifest.exists():
        return {'present': False}
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT / name
        need(path.is_file() and sha(path) == digest, 'Manifest mismatch: ' + name)
        count += 1
    return {'present': True, 'files': count, 'all_hashes_match': True}

def main():
    need(__debug__ and not sys.flags.optimize,
         'Do not use Python -O or PYTHONOPTIMIZE: inherited verifiers use assertions.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true')
    ap.add_argument('--receipt', type=Path, help='Optional separate output receipt path')
    args = ap.parse_args()
    started = time.monotonic()
    integrity = manifest_check()
    provenance = json.loads((ROOT/'PROVENANCE.json').read_text())
    for item in provenance['unchanged_inputs']:
        need(sha(ROOT/item['file']) == item['sha256'], 'Changed inherited input: '+item['file'])
    temp = Path(tempfile.mkdtemp(prefix='pa194hs-replay-'))
    packet = temp/'packet'
    packet.mkdir()
    for folder in ['construction','machines','verification','references']:
        shutil.copytree(ROOT/folder, packet/folder,
                        ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.log'))
    commands = []
    def run(label, argv, cwd=packet):
        print('Checking ' + label, flush=True)
        out = temp/(label+'.log')
        with out.open('w') as stream:
            result = subprocess.run([sys.executable,'-B',*map(str,argv)], cwd=cwd,
                                    stdout=stream, stderr=subprocess.STDOUT)
        need(result.returncode == 0, 'Failed '+label+'; inspect '+str(out))
        commands.append({'check':label,'status':'PASS','log_sha256':sha(out)})

    families = ['PA194H','PA194HS']
    for family in families:
        output = packet/'machines'/family
        run('build_'+family, ['construction/build_hybrid.py','--family',family[5:],
                              '--output',output])
        names = ['machine.tm','machine.native.tm','raw.native.tm','source.json',
                 'instructions.json','sites.json','labels.json','folds.json','fold_cases.json']
        for name in names:
            need((output/name).read_bytes() == (ROOT/'machines'/family/name).read_bytes(),
                 family+' reconstruction differs: '+name)
        bound = json.loads((ROOT/'machines'/family/'independent/receipt.json').read_text())
        need(bound['status']=='PASS', family+' independent record is not PASS')
        for field, name in [('dense_sha256','machine.tm'),('native_sha256','machine.native.tm'),
                            ('source_sha256','source.json')]:
            need(bound[field]==sha(output/name), family+' independent binding differs: '+field)
        need(bound['contracts_sha256']==sha(ROOT/'machines'/family/'independent/contracts.json'),
             family+' independent contract digest differs')

    run('source_splices', ['verification/check_source_splices.py'])
    run('command_words', ['construction/mathematics/check_hybrid_words.py'])
    for family in families:
        run('novelty_'+family, [ROOT/'comparison/compare_candidate.py',
                               ROOT/'machines'/family/'machine.tm',
                               '--census',ROOT/'comparison/current',
                               '--output',temp/('novelty_'+family+'.json')])
        novelty = json.loads((temp/('novelty_'+family+'.json')).read_text())
        need(novelty['matches']==[] and novelty['corpus_forms_of_same_size']==51,
             family+' graph novelty failed')
    if args.full:
        for family in families:
            run('independent_'+family, ['verification/check.py',packet/'machines'/family])
            for name in ['receipt.json','contracts.json','list_lemmas.json','blank_seed.json']:
                actual = packet/'machines'/family/'independent'/name
                recorded = ROOT/'machines'/family/'independent'/name
                need(actual.read_bytes()==recorded.read_bytes(),
                     family+' independent replay differs: '+name)
    result = {
        'status':'PASS','source_commit':provenance['pinned_commit'],
        'mode':'full' if args.full else 'default','release_integrity':integrity,
        'unchanged_inherited_input_hashes_checked':len(provenance['unchanged_inputs']),
        'literal_reconstruction_exact':True,'source_splices_checked':True,
        'hybrid_command_identities_checked':True,
        'construction_universal_contracts_replayed':True,
        'independent_universal_contracts_replayed':args.full,
        'recorded_independent_bindings_checked':True,'whole_blank_startups_checked':True,
        'all_current_194_state_byte_forms_compared':51,
        'no_cosmetic_matches':True,'sub194_machine_claimed':False,
        'kernel_checked_PA_endpoint':False,'checks':commands,
        'elapsed_seconds':round(time.monotonic()-started,3),
        'fresh_evidence_directory':str(temp)
    }
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
