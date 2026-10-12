"""Reproduce full-signature comparisons and original-source certificate audits."""
import itertools
import json
import random
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'experiments')]
from pattern_kernel.core import Tile,Block,expand,certify_cubic_graph,chain_payload
from pattern_kernel.signatures import tile_table,power
from routed_patterns import build_kernel,solve,verify_result
from routing_oracle import graph_table
from routing_families import star_triangle,connected_context,routed_beads


def random_aligned(rng,width):
    # Random nonempty partition, then permute whole component blocks.
    labels=[rng.randrange(width) for _ in range(width)]
    parts=sorted({tuple(j for j in range(width) if labels[j]==a) for a in labels})
    perm=list(range(len(parts)));rng.shuffle(perm)
    n=2*width
    edges=[]
    for i,part in enumerate(parts):
        vertices=list(part)+[width+j for j in parts[perm[i]]]
        if rng.randrange(2):
            vertices.append(n);n+=1
        rng.shuffle(vertices)
        for j in range(1,len(vertices)):
            edges.append((vertices[j],vertices[rng.randrange(j)]))
        for _ in range(rng.randrange(4)):
            edges.append((rng.choice(vertices),rng.choice(vertices)))
    return Tile(n,tuple(edges),tuple(range(width)),tuple(range(width,2*width)))


def main():
    rng=random.Random(20261012)
    comparisons=0;entries=0;variable=0;max_edges=0
    for trial in range(240):
        width=1+trial%3
        tile=random_aligned(rng,width)
        for n in [1+rng.randrange(7),17+rng.randrange(37)]:
            kernel,plan,_=build_kernel((Block(tile,n),),close=False)
            expected=power(tile_table(tile),n)
            actual=graph_table(kernel)
            if expected!=actual:
                raise AssertionError(('signature mismatch',trial,n,tile))
            comparisons+=1;entries+=4*(1<<(2*width))
            max_edges=max(max_edges,len(kernel.edges))
        # Explicitly count genuinely unequal component interface sizes.
        from routed_patterns.core import components
        data=components(tile)
        variable+=any(len(g['left'])!=len(g['right']) for g in data['groups'])
    verdict_cases=0
    for perm in itertools.permutations(range(3)):
        for n in range(1,11):
            chain=(Block(routed_beads(perm),n),)
            result=solve(chain)
            direct,_=expand(chain)
            assert result['graph_proof']['verdict']==certify_cubic_graph(direct)['verdict']
            assert verify_result(chain,result)
            verdict_cases+=1
    examples=[]
    for name,chain in [
        ('routed_4097_bits',(Block(star_triangle(),2**4096+1),)),
        ('mixed_1025_bits',(Block(star_triangle(),2**1024+1),
                            Block(connected_context(),2**513+3))),
        ('positive_tetrahedron',(Block(star_triangle(),1),)),
    ]:
        result=solve(chain);assert verify_result(chain,result)
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(chain_payload(chain),indent=2)+'\n')
        (ROOT/'examples'/f'{name}_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
        examples.append({'name':name,'verdict':result['graph_proof']['verdict'],
                         'kernel_vertices':result['kernel']['n'],
                         'kernel_edges':len(result['kernel']['edges'])})
    report={'seed':20261012,'random_source_tiles':240,'complete_signature_comparisons':comparisons,
            'signature_entries_compared':entries,'unequal_component_width_sources':variable,
            'maximum_kernel_edges_in_signature_audit':max_edges,
            'explicit_cubic_verdict_comparisons':verdict_cases,
            'examples':examples,'all_passed':True}
    (ROOT/'results/routing_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
