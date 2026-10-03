#!/usr/bin/env python3
"""Check identity rejection and strict receipts using disposable release copies."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(ok,message):
    if not ok:
        raise RuntimeError(message)


def invoke(root, *args, optimized=False):
    return subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(root/'verify_release.py'),*args],capture_output=True,text=True,timeout=60)


def main():
    baseline = invoke(ROOT,'--verify-only')
    require(baseline.returncode == 0,'Baseline identity check failed: '+baseline.stderr)
    records = []
    cases = ['manifest-content','manifest-and-checksums','formerly-unchecked-code','boolean-for-integer-receipt',
             'unexpected-file','unexpected-directory','unexpected-symlink','missing-payload','malformed-checksums']
    for optimized in (False,True):
        for case in cases:
            with tempfile.TemporaryDirectory(prefix='report32-tamper-') as tmp:
                work = Path(tmp)/'moved-release'
                shutil.copytree(ROOT,work,copy_function=shutil.copy2)
                if case in ('manifest-content','manifest-and-checksums'):
                    path = work/'MANIFEST.json'
                    value = json.loads(path.read_text());value['file_count'] += 1
                    path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
                    if case == 'manifest-and-checksums':
                        sums = ''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(work).as_posix()+'\n' for p in sorted(work.rglob('*')) if p.is_file() and p.name!='SHA256SUMS')
                        (work/'SHA256SUMS').write_text(sums)
                elif case == 'formerly-unchecked-code':
                    # This helper is not invoked by ordinary scientific replay, but
                    # must nevertheless be identity checked before any code runs.
                    path = work/'build_release_inventory.py';path.write_bytes(path.read_bytes()+b'\n# corruption probe\n')
                elif case == 'boolean-for-integer-receipt':
                    path = work/'paired/evidence/accepting-cli-check.json'
                    value = json.loads(path.read_text());value['sos'] = False
                    path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
                elif case == 'unexpected-file':
                    (work/'unexpected.py').write_text('raise RuntimeError("must never execute")\n')
                elif case == 'unexpected-directory':
                    (work/'unexpected-directory').mkdir()
                elif case == 'unexpected-symlink':
                    (work/'unexpected-link').symlink_to('core/compiler.py')
                elif case == 'missing-payload':
                    (work/'core/compiler.py').unlink()
                else:
                    path = work/'SHA256SUMS';path.write_bytes(path.read_bytes()+b'\n')
                # Request a complete replay: corruption must still stop at the gate.
                done = invoke(work,'--replay',optimized=optimized)
                require(done.returncode != 0,'Corrupted release accepted: '+case)
                require('Identity gate:' in done.stderr,'Failure was not an identity rejection: '+case)
                records.append({'case':case,'optimized':optimized,'identity_gate_rejected':True})
    types = {}
    for mode, optimized in [('normal',False),('optimized',True)]:
        done = invoke(ROOT,'--self-test-types',optimized=optimized)
        require(done.returncode == 0,'Semantic regression failed')
        types[mode] = json.loads(done.stdout)
    require(types['normal'] == types['optimized'],'Semantic regressions differ by mode')
    print(json.dumps({'schema':'report32-tamper-regression-v1','status':'PASS','cases':records,
                      'strict_semantic_mutations':types,'copied_scientific_code_executed_on_tampered_tree':False},indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
