"""Check the rooted disjointness obstruction at cycle-envelope rank zero."""
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'reports/72'))
from rooted_disc.kernel import State,direct_compatibility,pairing,binary_rank
from rooted_disc.mesh import replay_pair


def candidate(r,mask):
    partition=[0];next_block=1
    for i in range(r-1):
        if mask>>i&1:partition.append(0)
        else:partition.append(next_block);next_block+=1
    return State(tuple(partition),(True,)*next_block,(0,)*next_block)


def cap(r,mask):
    return State(tuple(range(r)),(True,)+tuple(not(mask>>i&1) for i in range(r-1)),(0,)*r)


records=[];entries=meshes=queries=0
for r in range(1,7):
    size=1<<(r-1);matrix=[]
    left=[candidate(r,x) for x in range(size)];right=[cap(r,b) for b in range(size)]
    for x,s in enumerate(left):
        row=0
        for b,t in enumerate(right):
            expected=not(x&b)
            assert direct_compatibility(s,t)==pairing(s,t)==expected
            row|=int(expected)<<b;entries+=1
            if r<=5:
                assert replay_pair(s,t).succeeds(0)==expected;meshes+=1
        matrix.append(row)
    assert binary_rank(matrix)==size
    for x in range(size):
        b=(size-1)^x
        eligible=[y for y in range(size) if not(y&b)]
        best=min(r-1-y.bit_count() for y in eligible)
        assert [y for y in eligible if r-1-y.bit_count()==best]==[x]
        queries+=1
    records.append(dict(arcs=r,coarse_left_blocks=1,coarse_right_blocks=r,
        cycle_overlap=r+1-1-r,matrix_rank=size,forced_original_witnesses=size))
paths=['reports/72/rooted_disc/kernel.py','reports/72/rooted_disc/mesh.py',
       'reports/72/rooted_disc/assembly.py','synthesis/data/rooted_tree_envelope.py']
result=dict(matrix_entries=entries,literal_mesh_pairs=meshes,uniquely_exposed_optima=queries,
    records=records,scope='abstract rooted disc-component continuation, not a fixed embedded knot-region lower bound',
    source_sha256={p:sha256((ROOT/p).read_bytes()).hexdigest() for p in paths})
(ROOT/'synthesis/data/rooted-tree-envelope.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('records','source_sha256')}))
