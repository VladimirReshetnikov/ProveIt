#!/usr/bin/env python3
"""Guarded two-sibling replay of the model negative-ordinate residue."""
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
ROOT = HERE.parents[1]
SOURCE = HERE/'ModelBNegativeResidue.lean'
DISCRETE = ROOT/'Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean'
NEGATIVE = ROOT/'Lean/DiophantineConsistency/ArithmeticNegativeNorms.lean'
MODEL = ROOT/'Lean/DiophantineConsistency/ModelArithmetic.lean'
ODD = ROOT/'Lean/DiophantineConsistency/ArithmeticOddOrdinateResidue.lean'
PAIR = Path('/tmp/ipra-ordinary12-coexistence-pair-01')
TERMINAL = Path('/tmp/ipra-ordinary12-coexistence-launch-terminal-01.json')
COMPARATOR = ROOT/'research/fresh-project-closure/compare.py'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PINS = {
    SOURCE: '13f370a5127ca9a9b53a127f05d5196b27c645cfc127710128487d48e9c45476',
    DISCRETE: '3870325628b4148b2825e1af96bbec91ecbb115e2e57a83d580df97ea53f07aa',
    NEGATIVE: '00c0a3b6bbddd9d6ea23d1e1ecbcc2e02f383a76e7618f6328288d413719d7ef',
    MODEL: '2a713070369ddcc404ad01f0c16d0d7cb9102acc21aac5d7eaef79dfd3182bc6',
    ODD: 'cb4080289e247320fe8f5930c471ceb02c5ad01fc6cb73cbdd813468ade7fa7c',
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
    if out.parent.resolve(strict=True) != Path('/tmp').resolve() or not out.name.startswith('ipra-thirteen-negative-residue-pair-'):
        raise ValueError('output must be a fresh /tmp/ipra-thirteen-negative-residue-pair-* directory')
    if out.exists() or out.is_symlink():
        raise ValueError('output already exists')
    check_pins()
    before = compare_parent()
    out.mkdir()
    runs = []
    for label in ('author','peer'):
        run = out/label
        root = run/'src'
        srcdir = root/'DiophantineConsistency'
        project = run/'lib/DiophantineConsistency'
        parent = PAIR/label/'child-output/lib'
        srcdir.mkdir(parents=True)
        project.mkdir(parents=True)
        (run/'lib/BusyBeaver').symlink_to(parent/'BusyBeaver',target_is_directory=True)
        seedlinks = {}
        for source in (parent/'DiophantineConsistency').glob('*.olean'):
            link = project/source.name
            link.symlink_to(source)
            seedlinks[str(link)] = H(source)
        env = os.environ.copy()
        for key in tuple(env):
            if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
                env.pop(key,None)
        env['LEAN_PATH'] = str(run/'lib')+':'+str(PACKAGE)
        row = {'label':label,'modules':[]}
        for source in (DISCRETE,NEGATIVE,MODEL,ODD,SOURCE):
            src = srcdir/source.name
            obj = project/(source.stem+'.olean')
            if obj.exists() or obj.is_symlink():
                raise ValueError(('unintended inherited object',str(obj)))
            shutil.copyfile(source,src)
            cmd = [str(LEAN),'-M4000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
            result = subprocess.run(cmd,env=env,text=True,capture_output=True,timeout=240)
            output = result.stdout+result.stderr
            if result.returncode or 'error:' in output or 'sorryAx' in output or 'admit' in output:
                raise ValueError(('Lean failed',label,source.name,result.returncode,output))
            reports = re.findall(r"^'[^']+' depends on axioms: \[([^\]]*)\]$",output,re.M)
            if source == SOURCE:
                if result.stderr or 'warning:' in output or len(reports) != 1:
                    raise ValueError(('unexpected seed output',label,output))
                if {x.strip() for x in reports[0].split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
                    raise ValueError(('unexpected axiom',label,reports))
            deps = subprocess.run([str(LEAN),'--deps',str(src)],env=env,text=True,capture_output=True,timeout=60)
            expected = {str(PACKAGE/'Init.olean')}
            if source == DISCRETE:
                expected |= {str(PACKAGE/'Mathlib/Data/ZMod/Basic.olean'),str(PACKAGE/'Mathlib/Tactic/Linarith.olean'),str(PACKAGE/'Mathlib/Tactic/Ring.olean')}
            elif source == NEGATIVE:
                expected |= {str(PACKAGE/'Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean'),str(PACKAGE/'Mathlib/Tactic/Ring.olean')}
            elif source == MODEL:
                expected |= {str(PACKAGE/'Mathlib/Tactic/LinearCombination.olean'),str(project/'ModelDifferenceRing.olean'),str(project/'DiscreteOrderedRingFacts.olean'),str(project/'ArithmeticNegativeNorms.olean')}
            elif source == ODD:
                expected |= {str(project/'ArithmeticPellHalfIndex.olean'),str(project/'ArithmeticPellClassification.olean'),str(project/'ArithmeticPellResidueClasses.olean'),str(project/'ModelArithmetic.olean')}
            else:
                expected |= {str(project/'ArithmeticOddOrdinateResidue.olean')}
            if deps.returncode or deps.stderr or set(deps.stdout.splitlines()) != expected:
                raise ValueError(('unexpected direct imports',label,source.name,deps.returncode,deps.stdout,deps.stderr))
            if H(src) != PINS[source]:
                raise ValueError(('copied source drift',label,source.name))
            row['modules'].append({'name':source.stem,'exit':result.returncode,'stdout':result.stdout,'stderr':result.stderr,
                                   'source_sha256':H(src),'object_sha256':H(obj),'axiom_reports':reports,
                                   'command':cmd,'deps_exit':deps.returncode,'deps_stdout':deps.stdout})
        for link, digest in seedlinks.items():
            if not Path(link).is_symlink() or H(link) != digest:
                raise ValueError(('parent link drift',link))
        row['parent_links_sha256'] = seedlinks
        runs.append(row)
    if [m['object_sha256'] for m in runs[0]['modules']] != [m['object_sha256'] for m in runs[1]['modules']]:
        raise ValueError('suffix objects do not match')
    if runs[0]['modules'][-1]['stdout'] != runs[1]['modules'][-1]['stdout']:
        raise ValueError('seed axiom reports do not match')
    check_pins()
    after = compare_parent()
    if before != after:
        raise ValueError('parent comparison changed')
    receipt = {'status':'PASS_PAIRED_THIRTEEN_NEGATIVE_RESIDUE','runs':runs,'parent_comparison':after,
               'fixed_inputs_sha256':{str(p):h for p,h in PINS.items()},
               'scope':'Two bounded model-level suffix compilations over the matched 70-module source-current parent. No positive carrier construction, 13-variable converse, iPRA proof, fixed-port calibration, Foundation outer-wrapper exit, or full package-transitive/dynamic audit is claimed.'}
    with (out/'receipt.json').open('x') as f:
        json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
    print('PASS_PAIRED_THIRTEEN_NEGATIVE_RESIDUE',H(out/'receipt.json'),flush=True)

if __name__ == '__main__':
    main()
