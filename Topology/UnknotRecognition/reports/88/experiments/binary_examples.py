import json,math,time
from pathlib import Path
from families import permuted_prisms,cap_prism
from cycle_kernel import Graph,kernel_power
from cycle_kernel.partitions import boundary_partition
root=Path(__file__).resolve().parents[1]
for name,t,n in [('huge-permuted-prism',permuted_prisms([2]),2**16384+1),('huge-cap-prism',cap_prism(),2**4096+7)]:
    (root/'examples'/f'{name}.json').write_text(json.dumps(dict(tile=t.to_dict(),exponent_hex=hex(n),threshold=3),indent=2)+'\n')
ells=[5,7,11,13,17,19,23];w=sum(ells);pi=list(range(w));base=0
for ell in ells:
    for i in range(ell):pi[base+i]=base+(i+1)%ell
    base+=ell
t=Graph(2*w,tuple((i,w+pi[i]) for i in range(w)),tuple(range(w)),tuple(range(w,2*w)))
n=2**16384+1;start=time.perf_counter();g,meta=kernel_power(t,n);elapsed=time.perf_counter()-start
# Independent powering by permutation squaring, not by cycle residues.
a=list(range(w));b=pi[:];e=n
while e:
    if e&1:a=[b[a[i]] for i in range(w)]
    b=[b[b[i]] for i in range(w)];e>>=1
reference=Graph(2*w,tuple((i,w+a[i]) for i in range(w)),tuple(range(w)),tuple(range(w,2*w)))
assert boundary_partition(g)==boundary_partition(reference)
(root/'experiments/global-period.json').write_text(json.dumps(dict(cycle_lengths=ells,width=w,permutation_order=math.lcm(*ells),
    exponent_bits=n.bit_length(),kernel_vertices=g.n,kernel_edges=len(g.edges),construction_seconds=elapsed,
    reference='independent repeated-squaring permutation routing',status='PASS'),indent=2)+'\n')
print((root/'experiments/global-period.json').read_text())
