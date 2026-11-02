#!/usr/bin/env python3
"""Bounded paired suffix replay against the matched coherent 70-module parent."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('replay rejects optimized Python')

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = HERE/'FreeJSignedTransport.lean'
SOURCE_SHA = 'dd2608fd773126ebe37cb0bd921fcb4cc06467e36e4be61aff050fa40dc2a116'
PAIR = Path('/tmp/ipra-ordinary12-coexistence-pair-01')
TERMINAL = Path('/tmp/ipra-ordinary12-coexistence-launch-terminal-01.json')
COMPARATOR = ROOT/'research/fresh-project-closure/compare.py'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS = {
    SOURCE: SOURCE_SHA,
    TERMINAL: 'dd70025565c88c3c59232bcb1c5e8cc3160db81c6e19ad3432672d535d92de0b',
    PAIR/'pair-state.json': 'a6a5a7ea24d392807c7b98ec989392084f5fdeb88bc5a5c8179f439fbcd6ef33',
    PAIR/'author/child-output/state.json': 'fceb7b4dbdc132fc37c4b0e82633b2547be7b27c0f1b414debfa6796fa114049',
    PAIR/'peer/child-output/state.json': 'ce847b696f9d9912166f7ca4cc01ba45268732b2c146a88eb73d21dc893e63f4',
    COMPARATOR: '530def48c58dc38ce8a293a5c9912762b2ad101e63faf7cb0763f71a7ac9a3a5',
    LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()


def check_pins():
    for p, digest in PINS.items():
        if H(p) != digest:
            raise ValueError(('fixed input drift',str(p)))
    terminal = json.loads(TERMINAL.read_text())
    pair = json.loads((PAIR/'pair-state.json').read_text())
    if terminal.get('status') != 'OBSERVED_PAIR_TERMINAL' or terminal.get('outer_exit_code') != 0:
        raise ValueError('launcher terminal is not a recorded exit zero')
    if pair.get('status') != 'MATCHED_PASS' or pair.get('comparison',{}).get('exit') != 0:
        raise ValueError('parent pair is not matched')


def compare_parent():
    cmd = [sys.executable,'-I','-S',str(COMPARATOR),str(PAIR/'author/child-output/state.json'),str(PAIR/'peer/child-output/state.json')]
    result = subprocess.run(cmd,text=True,capture_output=True,timeout=120)
    if result.returncode:
        raise ValueError(('parent comparator failed',result.returncode,result.stdout,result.stderr))
    data = json.loads(result.stdout)
    if data.get('status') != 'MATCHED_PASS' or data.get('rows') != 70 or result.stderr:
        raise ValueError(('unexpected parent comparator output',data,result.stderr))
    return data


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,required=True)
    args = ap.parse_args()
    out = args.output.absolute()
    if out.parent.resolve(strict=True) != Path('/tmp').resolve() or not out.name.startswith('ipra-freej-signed-transport-replay-'):
        raise ValueError('output must be a fresh /tmp/ipra-freej-signed-transport-replay-* directory')
    if out.exists() or out.is_symlink():
        raise ValueError('output already exists')
    check_pins()
    parent_before = compare_parent()
    out.mkdir()
    runs = []
    for label in ('author','peer'):
        root = out/label/'src'
        root.mkdir(parents=True)
        src = root/'FreeJSignedTransport.lean'
        shutil.copyfile(SOURCE,src)
        obj = out/label/'FreeJSignedTransport.olean'
        lib = PAIR/label/'child-output/lib'
        env = os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH'] = str(lib)+':'+str(PACKAGE)
        cmd = [str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
        result = subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=180)
        output = result.stdout+result.stderr
        reports = re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
        if result.returncode or result.stderr or 'warning:' in output or 'sorryAx' in output or len(reports) != 3:
            raise ValueError(('Lean failed or unexpected reports',label,result.returncode,output))
        if any({x.strip() for x in report.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for report in reports):
            raise ValueError(('unexpected axiom',label,reports))
        deps = subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
        expected = {str(PACKAGE/'Init.olean'),str(lib/'DiophantineConsistency/ModelDifferenceRing.olean'),str(lib/'DiophantineConsistency/FreeJNormZero.olean')}
        if deps.returncode or deps.stderr or set(deps.stdout.splitlines()) != expected:
            raise ValueError(('unexpected direct imports',label,deps.returncode,deps.stdout,deps.stderr))
        if H(src) != SOURCE_SHA:
            raise ValueError(('copied source drift',label))
        runs.append({'label':label,'exit':result.returncode,'stdout':result.stdout,'stderr':result.stderr,
                     'command':cmd,'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,
                     'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
    if runs[0]['object_sha256'] != runs[1]['object_sha256'] or runs[0]['stdout'] != runs[1]['stdout']:
        raise ValueError('suffix objects or axiom reports do not match')
    check_pins()
    parent_after = compare_parent()
    if parent_before != parent_after:
        raise ValueError('parent comparison changed')
    receipt = {'status':'PASS_PAIRED_FREEJ_SIGNED_TRANSPORT','runs':runs,'parent_comparison':parent_after,
               'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
               'scope':'Two bounded model-level suffix compilations over the matched 70-module source-current parent; no iPRA derivation, denominator integrality, descent termination, checker calibration, Foundation outer-wrapper exit, or package-transitive/dynamic ancestry audit is claimed.'}
    with (out/'receipt.json').open('x') as f:
        json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_FREEJ_SIGNED_TRANSPORT',H(out/'receipt.json'),flush=True)

if __name__ == '__main__':
    main()
