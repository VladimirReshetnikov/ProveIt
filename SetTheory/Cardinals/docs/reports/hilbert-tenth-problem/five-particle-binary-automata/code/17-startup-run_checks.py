#!/usr/bin/env python3
"""Non-mutating offline replay in independent fresh normal and -O copies.
Release-author option --record replaces only canonical generated outputs and
replay-receipt.json after both modes pass and agree. Rewrite the manifest after
using that option. Standard replay is read-only on the supplied package.
"""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
from verify_pins import verify_inputs, SOURCE_SHA256
ROOT=Path(__file__).resolve().parent
STAGES=('verify_pins.py','check_primary_table.py','verify_virtual3.py',
        'validate_source.py','verify_affine.py','independent_audit.py',
        'class_expansion_ledger.py','test_loader.py','test_concrete.py',
        'verify_initialization.py','independent_relabel_check.py',
        'verify_exact_delta.py','verify_rebuild.py','verify_orientation_pins.py')
OUTPUTS=('primary-table-receipt.json','schema-injection-receipt.json',
         'affine-receipt.json','independent-audit-receipt.json',
         'class-expansion-ledger.json','loader-api-receipt.json',
         'concrete-receipt.json','prologue-predicted-clocks.json',
         'target-ledger.json','loader-empty-tape.json','initialization-receipt.json',
         'empty-prologue-five-trace.json','empty-prologue-literal-trace.json',
         'empty-first-tm-five-trace.json','empty-first-tm-literal-trace.json',
         'empty-through-first-tm-literal-trace.json','independent-relabel-receipt.json',
         'exact-delta-receipt.json','byte-exact-rebuild-receipt.json',
         'baseline-rebuild-receipt.json','orientation-addendum/pin-verification-receipt.json')

def sha(raw):return hashlib.sha256(raw).hexdigest()
def inventory(root):
    return {p.relative_to(root).as_posix():sha(p.read_bytes()) for p in root.rglob('*') if p.is_file()}
def launch(copy, script, mode):
    command=[sys.executable,'-I','-B']+(['-O'] if mode=='optimized' else [])+[str(copy/'offline_stage.py'),str(copy/script)]
    environment=os.environ.copy()
    environment.pop('PYTHONPATH',None)
    environment.pop('PYTHONHOME',None)
    environment['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run(command,cwd=copy,text=True,capture_output=True,env=environment)
def require(condition, message):
    if not condition:raise RuntimeError(message)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record',action='store_true',help='release authors only: update canonical replay outputs before final manifest creation')
    args=parser.parse_args()
    sys.dont_write_bytecode=True
    verify_inputs()
    if not args.record:
        from verify_manifest import verify
        verify()
    original=inventory(ROOT)
    # Assert elimination must not silently remove a single verification condition.
    for name in STAGES:
        require(not any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse((ROOT/name).read_text()))), 'Optimization-sensitive assert in active stage: '+name)
    records=[]; artifacts=[]; unchanged=[]; negative=[]
    with tempfile.TemporaryDirectory(prefix='report17-offline-replay-') as temp:
        for mode in ('normal','optimized'):
            copy=Path(temp)/mode
            shutil.copytree(ROOT,copy)
            before=inventory(copy)
            current=[]
            for stage in STAGES:
                result=launch(copy,stage,mode)
                if result.returncode:
                    raise RuntimeError(mode+' stage '+stage+' failed:\n'+result.stdout+result.stderr)
                require(not result.stderr,mode+' unexpected stderr: '+stage+'\n'+result.stderr)
                current.append(dict(script=stage,status='PASS',stdout_sha256=sha(result.stdout.encode())))
                print(mode+': '+stage+' PASS',flush=True)
            data={name:(copy/name).read_bytes() for name in OUTPUTS}
            after=inventory(copy)
            allowed=set(OUTPUTS)
            require(set(after)==set(before)|allowed,'Unexpected replay byproduct')
            require(all(after[name]==digest for name,digest in before.items() if name not in allowed),'Replay changed an input, checker, or document')
            require(not any('__pycache__' in p.parts or p.suffix in ('.pyc','.log') for p in copy.rglob('*')),'Cache/log generated')
            # Missing/corrupted immutable data must fail, never become an optional check.
            target=copy/'dependency/tm_table.json';saved=target.read_bytes()
            target.write_bytes(saved+b' ')
            rejected=launch(copy,'verify_pins.py',mode)
            require(rejected.returncode!=0 and 'SHA-256 mismatch' in rejected.stderr,'Corrupt input accepted')
            target.write_bytes(saved)
            target=copy/'baseline/expected-outputs.json';saved=target.read_bytes();target.unlink()
            rejected=launch(copy,'verify_pins.py',mode)
            require(rejected.returncode!=0 and 'Missing/nonregular mandatory pinned input' in rejected.stderr,'Missing baseline pins accepted')
            target.write_bytes(saved)
            target=copy/'source.json';saved=target.read_bytes();target.write_bytes(saved+b' ')
            rejected=launch(copy,'verify_pins.py',mode)
            require(rejected.returncode!=0 and 'SHA-256 mismatch' in rejected.stderr,'Corrupt source accepted')
            target.write_bytes(saved)
            # Guard self-test: network construction and external data reads are denied.
            probe=copy/'_offline_probe.py'
            probe.write_text("import socket\nfrom pathlib import Path\nchecks=0\ntry: socket.socket()\nexcept RuntimeError: checks+=1\ntry: Path(__file__).resolve().parent.parent.joinpath('outside.txt').read_text()\nexcept RuntimeError: checks+=1\nif checks!=2: raise RuntimeError('Offline guard failure')\nprint('PASS: network and external-read guards')\n")
            (Path(temp)/'outside.txt').write_text('External data must not be read')
            guarded=launch(copy,probe.name,mode)
            require(guarded.returncode==0,'Offline guard self-test failed: '+guarded.stderr)
            probe.unlink()
            require(inventory(copy)==after,'Negative tests did not restore replay state')
            negative.append(dict(mode=mode,corrupt_input_rejected=True,corrupt_source_rejected=True,missing_baseline_pins_rejected=True,network_denied=True,external_data_read_denied=True))
            records.append(dict(mode=mode,python_flags=['-I','-B']+(['-O'] if mode=='optimized' else []),stages=current))
            artifacts.append(data)
            unchanged.append(dict(mode=mode,non_generated_files_unchanged=True,no_cache_or_log_byproducts=True))
        require(artifacts[0]==artifacts[1],'Normal and -O output artifacts disagree')
        require(records[0]['stages']==records[1]['stages'],'Normal and -O stage stdout disagrees')
        if not args.record:
            for name,raw in artifacts[0].items():
                require((ROOT/name).read_bytes()==raw,'Bundled output differs from fresh replay: '+name)
        require(inventory(ROOT)==original,'Source delivery was changed during isolated replay')
        receipt=dict(status='PASS',source_sha256=SOURCE_SHA256,scope='All active checks run in separate fresh isolated copies with mandatory known scientific-input pins, denied network and external data reads, no optional sibling-release dependencies, and exact normal/-O output agreement. No original/frozen directory is accessed.',modes=records,negative_controls=negative,copy_integrity=unchanged,generated_files={name:dict(bytes=len(raw),sha256=sha(raw)) for name,raw in sorted(artifacts[0].items())},limitations='Mathematical universality and compiler proofs are human-readable dependencies; executable finite checks do not constitute a formal proof assistant. Primary-paper visual provenance is historical. Predicted CA clocks are not CA execution.')
        if args.record:
            for name,raw in artifacts[0].items():(ROOT/name).write_bytes(raw)
            (ROOT/'replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2))

if __name__=='__main__':
    main()
