"""Independent dense-tape check of the exact 222-state blank initializer.

The finite tape allocation is guarded on every transition. The checked run
therefore equals the run on a two-way infinite zero tape. All unvisited cells
remain zero, and the final comparison covers the complete nonzero support.
"""
from pathlib import Path
import argparse,hashlib,json
if not __debug__:
    raise RuntimeError('Assertions must be enabled for this certificate checker.')

def verify(path):
    table={};start=None
    raw=Path(path).read_bytes()
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert (q,b) not in table and b in (0,1) and w in (0,1) and d in ('L','R')
        table[q,b]=w,1 if d=='R' else -1,z
    assert start==0
    states={q for q,b in table}
    assert len(states)==222 and len(table)==444 and 254 not in states
    assert set(table)=={(q,b)for q in states for b in(0,1)}
    assert {z for w,d,z in table.values()}-states=={254}
    lo,hi=-4096,4096;tape=bytearray(hi-lo+1);q=start;head=0
    minimum=maximum=0
    for tick in range(409835):
        assert lo<=head<=hi and q!=254
        bit=tape[head-lo];w,d,q=table[q,bit]
        tape[head-lo]=w;head+=d
        minimum=min(minimum,head);maximum=max(maximum,head)
    actual={lo+i for i,bit in enumerate(tape)if bit}
    expected={-6,176};position=177
    physical=[0,0,0,3,0,0,3,0,0]
    for value in physical+[1]*167:
        position+=1
        expected.update(range(position,position+value+1))
        position+=value+1
    assert q==84 and head==-5 and actual==expected
    return dict(status='DENSE_EXACT_BLANK_INITIALIZATION_PASS',
        working_states=222,transition_rows=444,table_sha256=hashlib.sha256(raw).hexdigest(),
        steps=409835,final_k_state=84,head=-5,header=176,zero_gap=181,
        logical_registers=[3,0,0,0,3,0,0,0,0],physical_registers=physical,
        spare_count=167,spare_values=1,one_cell_count=len(actual),
        one_cells=sorted(actual),visited_head_interval=[minimum,maximum],
        all_unlisted_cells=0,scope='Exact complete blank-tape run through transition 409835.')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table',type=Path,required=True)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=verify(args.table)
    if args.output:args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='one_cells'},indent=2))
