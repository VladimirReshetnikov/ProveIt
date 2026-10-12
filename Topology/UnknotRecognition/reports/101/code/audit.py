"""Reproducible finite/source audits; counters mean cases, not theorem proofs."""
from pathlib import Path
import sys,json,random,time,platform,hashlib
from collections import Counter
from itertools import permutations
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tests'))
from test_flags import catalog,gauge,one_tetra_sources
from atlas import *
from flags import *
from replay import verify
from sources import *
from reference import *
from morse_adapter import convex_cone_certificate,rm


def main():
    start=time.perf_counter(); rng=random.Random(2026101201)
    totals=Counter(); source_rows=[]; literal_rows=[]; source_hash=hashlib.sha256()
    for number,s in enumerate(one_tetra_sources()):
        totals['one_tetra_pairings_considered']+=1
        source_hash.update(dumps(s).encode())
        try: a,meta=tetrahedral_atlas(s)
        except ValueError as exc:
            if str(exc)!='nontrivial local-face holonomy': raise
            totals['one_tetra_rejected_face_holonomy']+=1
            source_rows.append({'id':number,'accepted':False,'reason':str(exc)})
            continue
        c=compile_flags(a); assert verify(a,c)
        counts=compare_source_oracle(s,meta,c); compare_compiled(a,c)
        x=expanded_cells(c.result)
        source_rows.append({'id':number,'accepted':True,**counts,'cells_by_dimension':inventory(c.result)['cell_counts'],
                            'homology_F2':homology(x[0],x[1],2),'homology_F3':homology(x[0],x[1],3),
                            'source_sha256':digest(a)})
        totals['one_tetra_accepted_source_cases']+=1
        totals['source_flag_oracle_cells']+=counts['cells']; totals['source_flag_oracle_covers']+=counts['covers']
        totals['symbolic_replays']+=1
    for p in permutations(range(4)):
        s=relabel_tetrahedra(solid_torus_source(),[p],[0]); a,meta=tetrahedral_atlas(s); c=compile_flags(a)
        assert verify(a,c); counts=compare_source_oracle(s,meta,c)
        totals['native_fixture_relabellings']+=1; totals['symbolic_replays']+=1
        totals['source_flag_oracle_cells']+=counts['cells']; totals['source_flag_oracle_covers']+=counts['covers']
    for p in catalog():
        for n in (1,2,4):
            a=polytope_ball(p,n); c=compile_flags(a); assert verify(a,c); counts=compare_compiled(a,c)
            packet,proof,critical=convex_cone_certificate(p,n,a,c); prepared=rm.prepare(packet)
            assert rm.verify_affine(prepared,proof) and rm.explicit_acyclic(prepared)
            assert len(rm.explicit_collapse_remainder(prepared))==n
            totals['convex_copy_cases']+=1; totals['explicit_cone_matching_checks']+=1; totals['symbolic_replays']+=1
            totals['literal_compared_cells']+=counts['cells']; totals['literal_compared_covers']+=counts['covers']
            literal_rows.append({'kind':'convex','polytope':p.name,'copies':n,**counts})
    for case in range(300):
        d=rng.randrange(3); n=rng.randint(1,12); periodic=bool(rng.randrange(2))
        base=polytope_ball(simplex(d)); a=product_with_line(base,n,periodic)
        if case%2: a=gauge(a,rng)
        c=compile_flags(a); assert verify(a,c); counts=compare_compiled(a,c)
        x=expanded_cells(c.result)
        assert homology(x[0],x[1],2)==((1,1,0,0) if periodic else (1,0,0,0))
        assert homology(x[0],x[1],3)==((1,1,0,0) if periodic else (1,0,0,0))
        totals['seeded_product_cases']+=1; totals['symbolic_replays']+=1
        totals['literal_compared_cells']+=counts['cells']; totals['literal_compared_covers']+=counts['covers']
        literal_rows.append({'kind':'product','case':case,'base_dimension':d,'segments':n,'periodic':periodic,**counts})
    for p in catalog():
        a=polytope_ball(p); c=compile_flags(a); second=compile_flags(c.result); assert verify(c.result,second)
        x=expanded_cells(second.result); regular_check(*x[:3]); assert abstract_simplex_check(x[0],x[1])
        totals['second_subdivision_cases']+=1; totals['symbolic_replays']+=1
    for b in (64,256,1024,4096,16384):
        n=(1<<b)+1; a=product_with_line(polytope_ball(simplex(2)),n,True); c=compile_flags(a)
        assert verify(a,c); text=dumps(certificate_data(c)); restored=certificate_from_data(loads(text)); assert verify(a,restored)
        assert len(c.result.families)==196 and len(c.result.charts)==1289
        totals['binary_stress_cases']+=1; totals['symbolic_replays']+=2
    a,meta=tetrahedral_atlas(solid_torus_source()); c=compile_flags(a); x=expanded_cells(c.result)
    result={'python':sys.version,'platform':platform.platform(),'seed':2026101201,'elapsed_seconds':time.perf_counter()-start,
            'totals':dict(totals),'enumerated_source_list_sha256':source_hash.hexdigest(),
            'native_fixture':{'source':solid_torus_source(),'source_atlas_sha256':digest(a),'regular_cells':inventory(c.result),
                              'homology_F2':homology(x[0],x[1]),'homology_F3':homology(x[0],x[1],3),
                              'boundary_homology_F2':homology(x[0],x[1],2,x[3]['boundary'])},
            'scope':'Finite tetrahedral source importer and generic affine atlas compiler; NOT full native normal-cut exporter or knot-recognition suite.',
            'one_tetra_cases':source_rows,'literal_cases':literal_rows}
    (ROOT/'results/audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'totals':dict(totals),'elapsed_seconds':result['elapsed_seconds']},indent=2))

if __name__=='__main__': main()
