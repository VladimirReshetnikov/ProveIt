"""Run only this companion's self-authored checkers, then verify exact outputs."""
from pathlib import Path
import hashlib, json, subprocess, sys, platform
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O or PYTHONOPTIMIZE.')
ROOT=Path(__file__).resolve().parents[1]

def main():
    subprocess.run([sys.executable,'-B',str(ROOT/'code/verify_manifest.py')],cwd=ROOT,check=True)
    if not (ROOT/'inputs/Dag254.v').is_file():
        raise SystemExit('Missing inputs/Dag254.v. Run code/fetch_inputs.py first (see README).')
    output=ROOT/'generated';output.mkdir(exist_ok=True)
    logs=output/'logs';logs.mkdir(exist_ok=True)
    scripts=['code/shifted_source.py','code/search_shapes.py','proof/check_shifted_pairing.py','independent-review/check.py']
    for rel in scripts:
        print('Running '+rel,flush=True)
        log=logs/(rel.replace('/','__')+'.log')
        with log.open('w') as stream:
            process=subprocess.run([sys.executable,'-B',str(ROOT/rel)],cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
        if process.returncode:
            print(log.read_text())
            raise RuntimeError(f'{rel} exited {process.returncode}')
    manifest=json.loads((ROOT/'EXPECTED_OUTPUTS.json').read_text())
    verified=[]
    for rel,spec in manifest.items():
        data=(output/rel).read_bytes()
        actual=hashlib.sha256(data).hexdigest()
        if len(data)!=spec['bytes'] or actual!=spec['sha256']:
            raise ValueError('Regenerated output differs: '+rel)
        verified.append({'path':rel,'bytes':len(data),'sha256':actual})
    receipt={'status':'PASS','python':platform.python_version(),'verified_outputs':verified,
             'downloaded_code_executed':False,'formal_kernel_build':False,'binary_machine_generated':False,
             'scope':'Exact source replacement, helper/interpreter tests, bounded shape costs, inductive clean-entry fixed points, mathematical finite checks, independent CFG audit. Abstract theorem arguments are reviewed mathematics; complete source/enumerator composition and literal-table/boot/frame-runtime proof remain separate obligations.'}
    (output/'REPRODUCTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(f'PASS: all {len(verified)} deterministic outputs match; generated/REPRODUCTION.json records scope')
if __name__=='__main__':
    main()
