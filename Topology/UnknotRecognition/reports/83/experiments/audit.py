"""Independent exhaustive-signature, brute-cut, and planar-dual audits."""
from __future__ import annotations
import itertools
import json
import platform
import random
import sys
import time
from pathlib import Path
from pattern_kernel import *
from pattern_kernel.core import certify_cubic_graph, Graph, chain_payload
from pattern_kernel.signatures import tile_table, power, multiply
from pattern_kernel.verify import _check_graph, verify_source_witness


def brute(g):
    best=4
    for bits in range(1<<g.n):
        cost=0;flags=0
        for a,b in g.edges:
            x,y=(bits>>a)&1,(bits>>b)&1
            if x!=y:cost+=1
            else:flags|=1<<x
        if flags==3:best=min(best,cost)
    return best


def dual_check(g):
    import networkx as nx
    planar, emb=nx.check_planarity(g)
    assert planar
    darts={}; faces=[]
    for v in g:
        for u in emb.neighbors_cw_order(v):
            if (v,u) in darts:continue
            face=emb.traverse_face(v,u); index=len(faces);faces.append(face)
            for a,b in zip(face,face[1:]+face[:1]):darts[a,b]=index
    d=nx.MultiGraph();d.add_nodes_from(range(len(faces)))
    for a,b in g.edges():d.add_edge(darts[a,b],darts[b,a])
    simple=all(a!=b and d.number_of_edges(a,b)==1 for a,b in d.edges())
    if not simple:return False
    h=nx.Graph(d)
    if len(h) in (3,4) and len(h.edges())==len(h)*(len(h)-1)//2:return True
    if len(h)<5:return False
    for k in range(4):
        for deleted in itertools.combinations(h,k):
            remaining=h.copy();remaining.remove_nodes_from(deleted)
            if not nx.is_connected(remaining):return False
    return True


def main():
    start=time.perf_counter();rng=random.Random(2026101204)
    signatures=1500;comparisons=0
    for _ in range(signatures):
        n=rng.randrange(2,9);w=rng.randrange(1,min(3,n//2)+1)
        edges=[(j,rng.randrange(j)) for j in range(1,n)]
        edges += [(rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(5))]
        t=Tile(n,tuple(edges),tuple(range(w)),tuple(range(w,2*w)))
        table=tile_table(t);current=power(table,4)
        for exponent in range(5,9):
            current=multiply(current,table)
            assert current==power(table,4)
            comparisons+=1
    random_graphs=180
    for _ in range(random_graphs):
        n=rng.choice([2,4,6,8,10]);stubs=[v for v in range(n) for _ in range(3)]
        rng.shuffle(stubs);g=Graph(n,tuple(zip(stubs[::2],stubs[1::2])))
        p=certify_cubic_graph(g);_check_graph(g,p)
        assert (brute(g)<=3)==(p['verdict']=='LOW_CYCLIC_CUT')
    import networkx as nx
    graphs=[nx.complete_graph(4),nx.cubical_graph(),nx.dodecahedral_graph()]
    graphs += [nx.circular_ladder_graph(n) for n in range(3,13)]
    g=nx.complete_graph(4)
    for _ in range(12):
        v=rng.choice(list(g));neighbors=list(g.neighbors(v));new=max(g)+1
        g.remove_node(v);a,b,c=new,new+1,new+2
        g.add_edges_from([(a,b),(b,c),(c,a)]+list(zip((a,b,c),neighbors)))
        graphs.append(g.copy())
    for g in graphs:
        h=nx.convert_node_labels_to_integers(g)
        p=certify_cubic_graph(Graph(len(h),tuple(h.edges())))
        assert (p['verdict']=='NO_LOW_CYCLIC_CUT')==dual_check(h)
    root=Path(__file__).resolve().parent.parent
    examples=root/'examples'
    big=(Block(prism_tile(),2**16384+1),)
    negative=(Block(prism_tile(),2**4096+7),Block(triangle_expansion_tile(),1),
              Block(prism_tile(),2**1024+9))
    sizes={}
    for name,chain in [('huge_prism',big),('huge_triangle_defect',negative)]:
        r=solve(chain);assert verify_result(chain,r)
        (examples/(name+'.json')).write_text(json.dumps(chain_payload(chain),indent=2)+'\n')
        text=json.dumps(r,indent=2)+'\n';(examples/(name+'_proof.json')).write_text(text)
        sizes[name]={'kernel_vertices':r['kernel']['n'],
                     'kernel_edges':len(r['kernel']['edges']),
                     'proof_bytes':len(text.encode()),'verdict':r['graph_proof']['verdict']}
        if 'source_witness' in r:
            addresses=verify_source_witness(chain,r['source_witness'])
            (examples/(name+'_source_addresses.json')).write_text(json.dumps(addresses,indent=2)+'\n')
            sizes[name]['source_cut_size']=addresses['cost']
    output={'seed':2026101204,'python':sys.version,'platform':platform.platform(),
            'signature_tiles':signatures,'four_copy_signature_comparisons':comparisons,
            'random_cubic_multigraphs':random_graphs,'independent_planar_dual_cases':len(graphs),
            'networkx_version':nx.__version__,'all_passed':True,'large_examples':sizes,
            'elapsed_seconds':time.perf_counter()-start,
            'native_recognizer_regression':'NOT_RUN',
            'native_knot_benchmarks':'NOT_RUN'}
    (root/'experiments/audit.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__=='__main__':main()
