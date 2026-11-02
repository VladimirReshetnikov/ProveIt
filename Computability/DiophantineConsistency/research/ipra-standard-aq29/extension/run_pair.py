#!/usr/bin/env python3
"""Run and compare two isolated selective rebuilds, preserving actual exits."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import prepare
from compare import compare

HERE=Path(__file__).resolve().parent
H=prepare.digest
p=argparse.ArgumentParser()
p.add_argument('--prepared',type=Path,required=True)
p.add_argument('--preparation-sha256',required=True)
p.add_argument('--old-snapshot',type=Path,required=True)
p.add_argument('--new-snapshot',type=Path,required=True)
p.add_argument('--expected-axiom-reports',type=int,required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
prepared=a.prepared.resolve(strict=True);out=a.output.absolute()
if out.exists() or out.is_symlink():raise ValueError('refusing to overwrite output')
if out.resolve().is_relative_to(prepared) or prepared.is_relative_to(out.resolve()):
    raise ValueError('coordinator output overlaps project outputs')
receipt=prepared/'preparation.json'
if H(receipt)!=a.preparation_sha256:raise ValueError('preparation hash mismatch')
preparation=json.loads(receipt.read_text());parent=Path(preparation['parent_pair']).resolve(strict=True)
parent_state=json.loads((parent/'author/state.json').read_text())
provider=Path(parent_state['provider']).resolve(strict=True)
provider_root=Path(json.loads(provider.read_text())['root']).resolve(strict=True)
toolchain=Path(parent_state['lean_path']).resolve(strict=True).parent.parent
for protected in (a.old_snapshot.resolve(strict=True),a.new_snapshot.resolve(strict=True),parent,
                  Path(parent_state['package_overlay']).resolve(strict=True),provider_root,toolchain):
    candidate=out.resolve()
    if candidate.is_relative_to(protected) or protected.is_relative_to(candidate):
        raise ValueError(('coordinator output overlaps protected root',str(protected)))
out.mkdir(parents=True,exist_ok=False)
state={'status':'RUNNING','runs':[],'preparation_sha256':a.preparation_sha256,
       'driver_sha256':H(HERE/'rebuild.py'),'comparator_sha256':H(HERE/'compare.py'),
       'coordinator_sha256':H(Path(__file__))}
def save():
    q=out/'pair-state.tmp';q.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');q.replace(out/'pair-state.json')
save()
try:
    for label in ('author','peer'):
        log=out/(label+'-process.log')
        cmd=[sys.executable,str(HERE/'rebuild.py'),'--prepared',str(prepared),
             '--preparation-sha256',a.preparation_sha256,'--old-snapshot',str(a.old_snapshot),
             '--new-snapshot',str(a.new_snapshot),'--sibling',label,
             '--expected-axiom-reports',str(a.expected_axiom_reports)]
        with log.open('x') as f:process=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
        builder_state=prepared/label/'rebuild-state.json'
        item={'label':label,'exit':process.returncode,'process_log':str(log),
              'process_log_sha256':H(log),'builder_state_sha256':H(builder_state) if builder_state.is_file() else None}
        state['runs'].append(item);save()
        if process.returncode:raise RuntimeError(('selective builder failed',label,process.returncode))
        print(label,'exit',process.returncode,flush=True)
    comparison=compare(prepared,a.old_snapshot,a.new_snapshot,a.preparation_sha256)
    for row in state['runs']:
        if H(row['process_log'])!=row['process_log_sha256'] or H(prepared/row['label']/'rebuild-state.json')!=row['builder_state_sha256']:
            raise RuntimeError(('builder evidence changed',row['label']))
    if H(HERE/'rebuild.py')!=state['driver_sha256'] or H(HERE/'compare.py')!=state['comparator_sha256'] or H(Path(__file__))!=state['coordinator_sha256']:
        raise RuntimeError('selective drivers changed')
    state.update(status='MATCHED_SELECTIVE_PASS',comparison=comparison);save()
    print('MATCHED_SELECTIVE_PASS',comparison['affected_modules'],'affected modules',flush=True)
except BaseException as exc:
    state.update(status='FAILED',failure=repr(exc));save();print('FAILED',repr(exc),flush=True);raise
