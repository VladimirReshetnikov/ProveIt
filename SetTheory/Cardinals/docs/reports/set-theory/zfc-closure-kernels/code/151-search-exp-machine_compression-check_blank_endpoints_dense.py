#!/usr/bin/env python3
"""Independent dense-array verification of three exact blank-start endpoints.
Only Python3's standard library is used. Expected tapes are constructed
straight from the stated frame specification; no runtime frame decoder is
imported or called. The result verifies a finite prefix, not equiconsistency.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
SPECS=(
    dict(name='baseline K218',file='baseline-k218.tm',steps=312909,
         state=84,head=-5,gap=80,counter=3,spares=130),
    dict(name='DMN K218',file='command-DMN-k218.tm',steps=123776,
         state=84,head=-4,gap=23,counter=2,spares=72),
    dict(name='Omit-zero-push K218',file='omit-zero-push-k218.tm',steps=312909,
         state=84,head=-5,gap=80,counter=3,spares=130),
)

def verify(spec,table_path):
    data=table_path.read_bytes();rows={}
    for line in data.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in rows
        rows[q,b]=(w,1 if d=='R' else -1,z)
    states={q for q,b in rows}
    assert len(states)==218 and len(rows)==436
    assert all((q,b) in rows for q in states for b in (0,1))
    assert all(z==254 or z in states for w,d,z in rows.values())

    # A head cannot travel farther than the number of executed steps.
    # Thus these finite arrays cover every cell that this prefix can visit.
    origin=spec['steps']+2;size=2*origin+1
    tape=bytearray(size);q=0;p=origin;visited_min=visited_max=p
    for _ in range(spec['steps']):
        w,d,q=rows[q,tape[p]]
        tape[p]=w;p+=d
        assert 0<=p<size
        visited_min=min(visited_min,p);visited_max=max(visited_max,p)
    assert q==spec['state'] and p-origin==spec['head']

    expected=bytearray(size);h=origin+spec['head']
    expected[h-1]=1
    header=h+64+spec['gap'];expected[header]=1
    # For logical (k,0,0,0,k,0,0,0,0), the specified physical
    # permutation gives these nine register values, followed by spares.
    physical=[0,0,0,spec['counter'],0,0,spec['counter'],0,0]
    physical.extend([1]*spec['spares'])
    p=header+1
    for value in physical:
        # Block B(value)=0 followed by value+1 ones.
        p+=1
        expected[p:p+value+1]=bytes([1])*(value+1)
        p+=value+1
    assert tape==expected, 'Complete dense tape differs from direct expected construction'
    ones=[i-origin for i,b in enumerate(tape)if b]
    receipt=dict(status='EXACT_DENSE_BLANK_ENDPOINT_PASS',name=spec['name'],
        table_file=table_path.name,table_sha256=hashlib.sha256(data).hexdigest(),
        working_states=218,steps=spec['steps'],state=spec['state'],head=spec['head'],
        gap=spec['gap'],logical_registers=[spec['counter'],0,0,0,spec['counter'],0,0,0,0],
        spare_values=[1]*spec['spares'],one_cell_count=len(ones),one_cells=ones,
        visited_interval=[visited_min-origin,visited_max-origin],
        complete_dense_tape_compared=True,frame_decoder_used=False,
        scope='Exact finite blank prefix and full endpoint tape only; not a proof of runtime simulation or Con(ZFC) equivalence.')
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--baseline',type=Path,default=HERE/SPECS[0]['file'])
    parser.add_argument('--dmn',type=Path,default=HERE/SPECS[1]['file'])
    parser.add_argument('--omit',type=Path,default=HERE/SPECS[2]['file'])
    parser.add_argument('--output',type=Path,default=HERE/'dense_blank_endpoints.json')
    args=parser.parse_args()
    results=[verify(SPECS[0],args.baseline),verify(SPECS[1],args.dmn),verify(SPECS[2],args.omit)]
    args.output.write_text(json.dumps(results,indent=2)+'\n')
    for r in results:
        print(f'{r["name"]}: PASS; {r["steps"]} steps, state {r["state"]}, head {r["head"]}, {r["one_cell_count"]} one cells; full dense tape equals direct expected frame.')
