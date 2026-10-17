"""Regenerate both tables and replay every transition to the exact handoff.

Default: compile the independent C++ simulator when a C++ compiler exists;
otherwise use exact Python simulation. Pass --python to force Python replay.
Resource or tool failures abort verification; they never mean acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

from build_bb5_initializer import build, HERE


def python_replay(table_path, target, limit):
    rows = {}
    for line in table_path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t = line.split()
        key=(int(q),int(b))
        if key in rows or d not in ('L','R'):
            raise ValueError('malformed or duplicate transition')
        rows[key]=(int(w),1 if d=='R' else -1,int(t))
    one=set(); q=h=0; lo=hi=0
    for step in range(1,limit+1):
        w,d,q=rows[q,int(h in one)]
        if w: one.add(h)
        else: one.discard(h)
        h+=d; lo=min(lo,h); hi=max(hi,h)
        if q==target:
            return dict(steps=step,state=q,head=h,visited_min=lo,
                        visited_max=hi,ones=sorted(one))
    raise RuntimeError('handoff not reached within exact bound')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--python',action='store_true')
    p.add_argument('--output',type=Path,default=HERE/'output')
    a=p.parse_args()
    m=build(HERE/'runtime_286.json',a.output)
    machine=a.output/'bb5_initializer_control_315.tm'
    compiler=shutil.which('g++') or shutil.which('clang++')
    if compiler and not a.python:
        with tempfile.TemporaryDirectory(prefix='bb5-initializer-') as temp:
            binary=Path(temp)/'replay_tm'
            result=Path(temp)/'result.json'
            subprocess.run([compiler,'-O3','-std=c++17',str(HERE/'replay_tm.cpp'),
                            '-o',str(binary)],check=True)
            subprocess.run([str(binary),str(machine),str(m['runtime_entry']),
                            str(m['exact_handoff_steps']),str(result)],check=True)
            replay=json.loads(result.read_text())
        method='independent C++ literal-table interpreter'
    else:
        replay=python_replay(machine,m['runtime_entry'],m['exact_handoff_steps'])
        method='Python sparse-tape literal-table interpreter'
    for key in ('head','steps','state','ones'):
        expected=dict(head=m['head'],steps=m['exact_handoff_steps'],
                      state=m['runtime_entry'],ones=m['expected_ones'])[key]
        if replay[key]!=expected:
            raise ValueError(f'incorrect {key}: {replay[key]!r}')
    # Independently recover the nine physical zero-register blocks.
    ones=set(replay['ones']); header=m['header']
    for j in range(1,19):
        if int(header+j in ones)!=(j+1)%2:
            raise ValueError('register block differs')
    if ones!={m['left_marker'],header,*range(header+2,header+19,2)}:
        raise ValueError('unexpected data outside frame')
    result=dict(status='PASS',method=method,working_states=m['working_states'],
                initializer_states=m['initializer_states'],
                runtime_rows_preserved=m['runtime_rows_preserved'],replay=replay,
                gap=m['gap'],minimum_runtime_gap=102,
                table_sha256=hashlib.sha256(machine.read_bytes()).hexdigest(),
                all_zero_initial_tape=True,full_runtime_theorem=False)
    (a.output/'initializer_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
