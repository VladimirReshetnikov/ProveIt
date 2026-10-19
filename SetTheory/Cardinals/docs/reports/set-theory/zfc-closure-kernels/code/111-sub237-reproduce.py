#!/usr/bin/env python3
"""Replay the research package using Python 3.10+ and its standard library.

Default: check the manifest, reconstruct/audit the preserved 237-state parent,
independently verify its final all-tape fold, regenerate and independently
check the new source invariant, and rebuild every new equational packet.
--full additionally reruns the parent's three universal symbolic jobs and the
new source-restricted runtime proof. Discovery searches are optional research.
All generated files go into a new output directory; delivered evidence stays
unchanged. Run without -O or -OO.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import traceback
import zipfile

ROOT = Path(__file__).resolve().parent
SOURCE_SHA = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
PARENT_SHA = 'e5e368406a17400d86a94714b6fd6140c80b0f28550233da6e5b829f1fe80286'
CANONICAL_SHA = '7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6'
CASE_SHA = '573e2d88400030c9457ab028c701102205124875f69aedd6acfa7f9341cd8c25'

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8'))

def stable(value):
    if isinstance(value, list):
        return [stable(x) for x in value]
    if isinstance(value, dict):
        return {k:stable(v) for k,v in value.items()
                if k not in ('seconds', 'elapsed_seconds', 'wall_time_seconds')}
    return value

def check_manifest():
    checked = {}
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, 'Malformed manifest entry')
        expected, name = match.groups()
        p = Path(name)
        require(not p.is_absolute() and '..' not in p.parts, 'Unsafe manifest path')
        require(name not in checked, 'Duplicate manifest path')
        actual = sha(ROOT/p)
        require(actual == expected, 'Manifest mismatch: '+name)
        checked[name] = actual
    require('reproduce.py' in checked and 'vendor/parent237.zip' in checked,
            'Manifest does not cover the replay program and parent')
    return checked

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full', action='store_true')
    ap.add_argument('--output-dir', type=Path, default=Path('replay'))
    args=ap.parse_args()
    require(__debug__, 'Assertions must remain enabled')
    out=args.output_dir.resolve()
    require(out != ROOT and not (out.exists() and any(out.iterdir())),
            'Use a new or empty output directory')
    out.mkdir(parents=True, exist_ok=True)
    (out/'logs').mkdir()
    record=dict(status='RUNNING', full=args.full, commands=[], comparisons=[],
                started_utc=datetime.now(timezone.utc).isoformat(),
                python_version=sys.version, scope='Mathematical and byte-level replay; no proof-assistant kernel build')
    began=time.monotonic()
    def save():
        (out/'replay.json').write_text(json.dumps(record,indent=2)+'\n')
    def run(name, arguments, cwd=ROOT):
        cmd=[sys.executable, '-B', *map(str,arguments)]
        log=out/'logs'/(f'{len(record["commands"])+1:02d}_'+name+'.log')
        entry=dict(name=name, command=cmd, cwd=str(cwd), log=str(log.relative_to(out)), status='RUNNING')
        record['commands'].append(entry);save();print('RUN',name,flush=True)
        env=os.environ.copy();env['PYTHONOPTIMIZE']='0';env['PYTHONDONTWRITEBYTECODE']='1'
        tick=time.monotonic()
        with log.open('w') as stream:
            process=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT)
            while True:
                try:
                    code=process.wait(timeout=30);break
                except subprocess.TimeoutExpired:
                    print('RUNNING',name,round(time.monotonic()-tick),'seconds',flush=True)
        entry.update(status='PASS' if code==0 else 'FAIL',returncode=code,
                     seconds=time.monotonic()-tick,log_sha256=sha(log))
        save();require(code==0, f'{name} failed; see {log}')
    def identical(a,b,name):
        require(a.read_bytes()==b.read_bytes(), 'Rebuilt bytes differ: '+name)
        record['comparisons'].append(dict(name=name,status='PASS_BYTE_IDENTITY',sha256=sha(a)))
    def same_json(a,b,name):
        require(stable(read(a))==stable(read(b)), 'Deterministic proof fields differ: '+name)
        record['comparisons'].append(dict(name=name,status='PASS_DETERMINISTIC_PROOF_FIELDS'))
    try:
        before=check_manifest()
        record['manifest']=dict(status='PASS',files=len(before),sha256=sha(ROOT/'SHA256SUMS'))
        require(sha(ROOT/'vendor/parent237.zip')==PARENT_SHA,'Parent archive identity changed')
        require(sha(ROOT/'machines/zfc_composed237.tm')==CANONICAL_SHA,'Canonical table changed')
        require(sha(ROOT/'evidence/universal237_fresh_cases.json')==CASE_SHA,'Fresh universal case array changed')
        source=ROOT/'research/source_abstraction'
        require(sha(source/'source.json')==SOURCE_SHA,'Source identity changed')
        with tempfile.TemporaryDirectory(prefix='zfc-research-replay-') as tmp:
            temp=Path(tmp)
            with zipfile.ZipFile(ROOT/'vendor/parent237.zip') as z:
                for member in z.infolist():
                    p=Path(member.filename)
                    require(not p.is_absolute() and '..' not in p.parts,'Unsafe parent archive path')
                    require((member.external_attr>>16)&0o170000 != 0o120000,'Archive symlink is not allowed')
                z.extractall(temp)
            parent=temp/'zfc237-research-20261019'
            require((parent/'reproduce.py').is_file(),'Expected parent package not found')
            flags=['--full'] if args.full else []
            run('parent237',[parent/'reproduce.py',*flags,'--output-dir',out/'parent'])
            for name in ('zfc_composed237.tm','zfc_composed237_old.tm','renumbering.json'):
                identical(out/'parent/rebuilt237'/name,ROOT/'machines'/name,name)
            run('all_tape_fold',[ROOT/'verification/verify_representation.py',
                parent/'zfc_composed238_old.tm',ROOT/'machines/zfc_composed237_old.tm',
                '--deleted','235','--retained','98','--radius','2','--old-cap','1','--new-cap','5',
                '--output',out/'independent237_representation.json'])
            same_json(out/'independent237_representation.json',ROOT/'evidence/independent237_representation.json','all-tape fold')
            run('source_invariant_discovery',[source/'verify_invariant.py','--threshold','16','--output',out/'source_generation'])
            for name in ('source_abstract_facts_k16.json','source_abstract_summary_k16.json'):
                identical(out/'source_generation'/name,source/name,name)
            run('source_invariant_independent',[ROOT/'verification/check_source_product_invariant.py',
                '--sites',source/'source.json','--facts',source/'source_abstract_facts_k16.json',
                '--summary',source/'source_abstract_summary_k16.json','--threshold','16',
                '--output',out/'source_product_k16_independent.json'])
            same_json(out/'source_product_k16_independent.json',ROOT/'evidence/source_product_k16_independent.json','independent source invariant')
            run('equational_packets',[ROOT/'equational/build704.py','--baseline',ROOT/'inputs/E713.bits','--out',out/'equational'])
            for expected in sorted((ROOT/'equational/generated').glob('E*.*')):
                identical(out/'equational'/expected.name,expected,expected.name)
            if args.full:
                identical(out/'parent/full/universal_runtime237_cases.json',ROOT/'evidence/universal237_fresh_cases.json','unrestricted 237 cases')
                run('source_restricted_runtime',[ROOT/'verification/check_source_restricted_runtime.py',
                    '--engine-dir',parent/'verification','--table',ROOT/'machines/zfc_composed237_old.tm',
                    '--states','237','--sites',source/'source.json',
                    '--facts',source/'source_abstract_facts_k16.json',
                    '--summary',source/'source_abstract_summary_k16.json','--threshold','16',
                    '--output',out/'restricted_runtime237.json'])
                expected=ROOT/'evidence/restricted_runtime237_cases.json'
                require(expected.is_file(),'Missing delivered restricted-runtime case array')
                identical(out/'restricted_runtime237_cases.json',expected,'source-restricted 237 cases')
        for name,expected in before.items():
            require(sha(ROOT/name)==expected, 'Delivered file changed during replay: '+name)
        record.update(status='PASS_FULL_REPLAY' if args.full else 'PASS_QUICK_REPLAY',
                      delivered_files_unchanged=True, temporary_parent_removed=True)
    except Exception as exc:
        record.update(status='FAIL',error=str(exc),traceback=traceback.format_exc())
        print('FAIL',str(exc),file=sys.stderr,flush=True)
    finally:
        record['seconds']=time.monotonic()-began;record['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print(record['status'],str(out/'replay.json'),flush=True)
    return 0 if record['status'].startswith('PASS') else 1

if __name__=='__main__':
    raise SystemExit(main())
