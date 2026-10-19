#!/usr/bin/env python3
"""Portable verification of the saved research outputs.

Default: symbolic formula checks, macro equivalences, source compilation,
affine instruction checks, bootstrap, exact table reproduction, and an
independent audit linked to the archived whole-frame certificate.
--whole-frame also recomputes the full arbitrary-tape symbolic induction.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert __debug__, 'Use Python with assertions enabled; do not use -O.'
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--whole-frame',action='store_true')
    p.add_argument('--build',type=Path,default=HERE/'build')
    p.add_argument('--prepare-only',action='store_true')
    args=p.parse_args()
    build=args.build.resolve()
    assert build!=HERE and build!=Path('/')
    build.mkdir(parents=True,exist_ok=True)
    logdir=build/'logs';logdir.mkdir(exist_ok=True)
    results=[]
    def run(label,command):
        start=time.monotonic()
        with (logdir/(label+'.log')).open('w') as log:
            completed=subprocess.run(list(map(str,command)),cwd=HERE,stdout=log,stderr=subprocess.STDOUT)
        if completed.returncode:
            print((logdir/(label+'.log')).read_text()[-5000:])
            raise RuntimeError(f'{label} failed with {completed.returncode}')
        record=dict(check=label,status='PASS',seconds=time.monotonic()-start,
                    command=list(map(str,command)))
        results.append(record);print(json.dumps({k:v for k,v in record.items() if k!='command'}),flush=True)
    manifest=HERE/'SHA256SUMS'
    if manifest.exists():
        lines=manifest.read_text().splitlines()
        for line in lines:
            digest,name=line.split('  ',1)
            target=HERE/name
            assert target.is_file() and sha(target)==digest, name
        print(f'PASS: {len(lines)} archived payload hashes',flush=True)
    reference=HERE/'reference/zfc245-proof-20261018.zip'
    provenance=json.loads((HERE/'PROVENANCE.json').read_text())
    expected=next(x['sha256'] for x in provenance['copied_payloads'] if x['path']=='reference/zfc245-proof-20261018.zip')
    assert sha(reference)==expected
    extracted=build/'reference';extracted.mkdir(exist_ok=True)
    with ZipFile(reference) as archive:
        for name in archive.namelist():
            path=Path(name)
            assert not path.is_absolute() and '..' not in path.parts
        archive.extractall(extracted)
    base=extracted/'zfc245-proof-20261018'
    runtime=build/'runtime'
    shutil.copytree(base,runtime,dirs_exist_ok=True)
    shutil.copytree(HERE/'work/fine_grammar/runtime/code',runtime/'code',dirs_exist_ok=True)
    if args.prepare_only:
        print(runtime);return
    logic=build/'logic'
    shutil.copytree(HERE/'work/theory_encoding',logic,dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns('__pycache__','basis_results','double_negation_results','vendor'))
    py=sys.executable
    run('dne-formula-interface',[py,logic/'check_dne_variants.py'])
    if (logic/'boolean_bundle_variants.py').exists():
        run('boolean-formula-interface',[py,logic/'boolean_bundle_variants.py','--check'])
    run('macro-fine-bridge',[py,HERE/'work/machine_reduction/audit_macro_fine_bridge.py',
        '--dag',logic/'snapshot/ZF/m254/coq/prog/Dag254.v',
        '--grammar',runtime/'inputs/closed-sequence-grammar-next22.json',
        '--macro-map',logic/'macro_to_fine.json',
        '--rmpath',runtime/'reference/jeff/ZF/m254/tools/prog/rmpath.py',
        '--output',build/'macro-fine-bridge.json','--certificates',build/'macro-fine-bridge-certificates.json'])
    run('locked-scanner-obstruction',[py,HERE/'work/grammar_search/locked_scanner_obstruction.py',
        runtime,'--output',build/'locked-scanner-obstruction.json'])
    run('locked-fine-scanner-obstruction',[py,HERE/'work/grammar_search/locked_fine_scanner_obstruction.py',
        build,'--candidate',HERE/'machine/grammar.json',
        '--output',build/'locked-fine-scanner-obstruction.json'])
    sys.path.insert(0,str(runtime/'code'))
    from audit_fine_grammar import audit,make_vocabulary
    variants=json.loads((logic/'original_layout_dne_variants.json').read_text())['variants']
    saved=json.loads((HERE/'machine/grammar.json').read_text())
    assert saved['source_override']['mask']==32
    assert saved['source_override']['new_word']==variants[32]['fine_AX']
    assert saved['source_override']['original_word']==variants[0]['fine_AX']
    grammar_report=audit(HERE/'machine/grammar.json',short_scan=True)
    assert grammar_report['working_states']==245
    reports=[]
    for candidate in sorted((HERE/'work/fine_grammar/dne-breadth').glob('mask*/candidate.json')):
        data=json.loads(candidate.read_text());mask=data['source_override']['mask']
        assert data['source_override']['new_word']==variants[mask]['fine_AX']
        reports.append(audit(candidate,short_scan=True))
    assert len(reports)==63
    (build/'saved-grammar-audits.json').write_text(json.dumps(dict(
        status='PASS',canonical=grammar_report,breadth_proposals=reports),indent=2)+'\n')
    print('PASS: exact normalized source and 63 independently checked saved grammar proposals',flush=True)
    machine=build/'normalized245'
    run('source-affine-blank',[py,runtime/'code/build_source_machine.py',HERE/'machine/grammar.json',
        machine,'--short-scan','--padding','64'])
    assert (machine/'machine.tm').read_bytes()==(HERE/'machine/normalized245.tm').read_bytes()
    assert sha(machine/'machine.tm')==provenance['canonical_table_sha256']
    frame=HERE/'certificates/normalized245/whole-frame.json'
    if args.whole_frame:
        frame=build/'whole-frame.json'
        run('whole-frame',[py,HERE/'work/machine_reduction/whole_frame_dynamic.py',
            '--runtime',runtime,'--table',machine/'machine_old.tm',
            '--sites',machine/'sites_physical.json','--padding','64',
            '--source-reference',machine/'modified_source.json','--output',frame])
    run('independent-frame',[py,HERE/'work/machine_reduction/audit_frame_dynamic.py',
        '--old-table',machine/'machine_old.tm','--table',machine/'machine.tm',
        '--renumbering',machine/'renumbering.json','--logical-sites',machine/'sites_logical.json',
        '--physical-sites',machine/'sites_physical.json','--bootstrap',machine/'blank_boot.json',
        '--whole-frame-report',frame,'--grammar',HERE/'machine/grammar.json',
        '--locks',HERE/'work/fine_grammar/fine-lock54.txt','--require-seed','3,0,0,0,3,0,0,0,0',
        '--output',build/'independent-frame-audit.json'])
    output=dict(status='PASS',working_states=245,sub245_machine_found=False,
                canonical_sha256=sha(machine/'machine.tm'),
                full_symbolic_replayed=args.whole_frame,
                default_frame_evidence='Fresh full symbolic replay' if args.whole_frame else 'Archived full replay linked by exact table/site hashes',
                checks=results,scope='Executable verification plus the explicit ordinary logical proof; no new proof-assistant endpoint.')
    (build/'reproduction-summary.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='checks'},indent=2))

if __name__=='__main__':
    main()
