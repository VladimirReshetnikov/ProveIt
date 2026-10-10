#!/usr/bin/env python3
"""Deterministic independent finite oracles; all counts derive from execution."""
import sys, json, random, time, platform
from pathlib import Path
from itertools import product
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from span_excess import *
from span_excess.network import feasibility, minimize_difference
from span_excess.checker import check_negative_cycle, check_optimum, check_feasible
from span_excess.prepare import prepare_model
from span_excess.strata import enumerate_strata, Stratum
from span_excess.geometry import product_solid_torus, expand_surface
from span_excess.pachner import from_product, moves23, move23, move14, replay_history


def interval_model(L):
    return prepare_model(4,[(0,1,2,3)]*2,[(0,0,0,0),(L,0,0,0)],
                         [(0,1,-L//3,2),(1,2,1,1),(2,3,-2,2)])


def run():
    rng=random.Random(20261009)
    data={'seed':20261009,'python':platform.python_version(),'platform':platform.platform(),
          'scope':'reference kernels and constructed triangulated solid tori; no native recognizer run'}
    started=time.perf_counter()
    flow_checks=potentials=feasible_cases=infeasible_cases=0
    for _ in range(600):
        n=rng.randrange(2,6)
        arcs=[]
        for v in range(1,n): arcs.extend(((0,v,3),(v,0,3)))
        for __ in range(rng.randrange(0,6)):
            arcs.append((rng.randrange(n),rng.randrange(n),rng.randrange(-4,5)))
        edges=[(rng.randrange(n),rng.randrange(n),rng.randrange(-5,6),rng.randrange(5))
               for __ in range(rng.randrange(0,9))]
        ans=minimize_difference(n,edges,arcs)
        values=[]
        for tail in product(range(-3,4),repeat=n-1):
            p=(0,)+tail;potentials+=1
            if all(p[v]-p[u]<=b for u,v,b in arcs):
                values.append(sum(w*abs(c+p[v]-p[u]) for u,v,c,w in edges))
        proof=ans['certificate']
        if values:
            assert check_optimum(n,edges,arcs,proof)
            assert proof['objective']==min(values)
            assert ans['stats']['augmentations']<=sum(w for u,v,c,w in edges)
            feasible_cases+=1
        else:
            assert check_negative_cycle(n,arcs,proof);infeasible_cases+=1
        flow_checks+=1
    data['flow']={'models':flow_checks,'boxed_potentials':potentials,
                  'feasible_models':feasible_cases,'infeasible_models':infeasible_cases}
    coverage=0;band_count=0;cell_count=0;box_count=0
    for i in range(80):
        n=2+i%2;t=2+i%2
        vs=[tuple(list(range(n))+[rng.randrange(n) for _ in range(4-n)]) for __ in range(t)]
        hs=[tuple(rng.randrange(-3,4) for _ in range(4)) for __ in range(t)]
        es=[(rng.randrange(n),rng.randrange(n),rng.randrange(-3,4),rng.randrange(4)) for __ in range(5)]
        m=prepare_model(n,vs,hs,es)
        for p in product(range(-2,3),repeat=n):
            cell=containing_stratum(m,p)
            assert sum(m.defects(p))==m.span(p)-m.optimum
            assert check_feasible(n,constraints_for(m,cell),p)
            coverage+=1
        k=i%3
        a=optimize_band(m,k)
        assert replay_band(m,a)
        # Every row contains every global vertex, so this is a proved full box.
        L=m.optimum+k+6
        best={}
        for tail in product(range(-L,L+1),repeat=n-1):
            p=(0,)+tail;box_count+=1;q=m.span(p)-m.optimum
            if q<=k:
                score=m.score2(p);best[str(q)]=max(best.get(str(q),score),score)
        assert best=={q:row['score2'] for q,row in a['profile'].items()}
        band_count+=1;cell_count+=a['stats']['strata']
    data['stratification']={'height_models':80,'membership_checks':coverage,
                            'complete_bands':band_count,'replayed_cells':cell_count,
                            'exhaustive_box_potentials':box_count}
    meshes=[];geometry_potentials=0;component_tests=0;max_components=max_genus=0
    euler_pairs=Counter();moves=Counter();lex_count=0;geometric_bands=0;geom_cells=0
    retained=[]
    for i in range(100):
        g=from_product(product_solid_torus(3+i%2,bool(i%3==0)))
        for j in range(8):
            options=list(moves23(g))
            if options and rng.random()<.7:
                g=move23(g,rng.choice(options));moves['2-3']+=1
            else:
                g=move14(g,rng.randrange(len(g.tetrahedra)));moves['1-4']+=1
        assert replay_history(g.history)==g
        m=g.model()
        lex=minimize_edge_then_span(m)
        assert replay_edge_then_span(m,lex)
        old=minimize_difference(m.n,m.edges,constraints_for(m,Stratum()),m.initial)['certificate']
        euler_pairs[(m.score2(old['potential']),lex['score2'])]+=1
        s=expand_surface(g,lex['potential'])
        assert len(s['components'])==1 and s['components'][0]['class']==1
        assert 2*s['euler']==lex['score2'];lex_count+=1
        potentials=[m.initial,old['potential'],lex['potential']]
        potentials += [tuple(rng.randrange(-2,3) for _ in range(g.n)) for __ in range(9)]
        for p in potentials:
            s=expand_surface(g,p);delta=s['pieces']-m.optimum
            assert 2*s['euler']==m.score2(p)
            assert sum(r['class'] for r in s['components'])==1
            assert len(s['components'])<=delta+1
            q=sum(r['class']==-1 for r in s['components'])
            assert 2*q*m.optimum<=delta
            null_mass=sum(r['pieces'] for r in s['components'] if r['class']==0)
            assert null_mass<=delta-2*q*m.optimum
            for f in s['components']:
                assert f['class'] in (-1,0,1)
                if f['class']==1:
                    assert s['pieces']-f['pieces']<=delta
                    component_tests+=1
                max_genus=max(max_genus,f['genus'])
            geometry_potentials+=1;max_components=max(max_components,len(s['components']))
        if i<8:
            band=optimize_band(m,1)
            assert replay_band(m,band)
            for row in band['profile'].values():
                assert 2*expand_surface(g,row['proof']['potential'])['euler']==row['score2']
            geometric_bands+=1;geom_cells+=band['stats']['strata']
        if i<3:
            retained.append({'geometry':g.to_dict(),'model':m.to_dict(),'lexicographic':lex})
        meshes.append({'n':g.n,'tetrahedra':len(g.tetrahedra),'span_min':m.optimum,
                       'span_lex':lex['span'],'score2_face':m.score2(old['potential']),
                       'score2_lex':lex['score2'],'history':g.history})
    data['geometry']={'constructed_meshes':100,'legal_moves':dict(moves),
                      'literal_surfaces':geometry_potentials,
                      'positive_core_budget_checks':component_tests,
                      'maximum_components_seen':max_components,'maximum_genus_seen':max_genus,
                      'lexicographic_connected_outputs':lex_count,
                      'complete_radius_one_bands':geometric_bands,'replayed_band_cells':geom_cells,
                      'face_to_lex_euler_pairs': [{'face_score2':a,'lex_score2':b,'count':v}
                                                 for (a,b),v in sorted(euler_pairs.items())]}
    # Sharp opposite-pair family, with fixed triangulation and growing integer heights.
    g=product_solid_torus();m=g.model();sharp=[]
    for q in range(25):
        p=[0]*3+[q]*3+[0]*3;s=expand_surface(g,p)
        assert s['pieces']==3*(2*q+1)
        assert sum(f['class']==-1 for f in s['components'])==q
        sharp.append({'q':q,'pieces':s['pieces'],'components':len(s['components']),
                      'excess':s['pieces']-m.optimum})
    data['sharp_opposite_pairs']={'cases':len(sharp),'minimum_span':3,'records':sharp}
    data['elapsed_seconds']=time.perf_counter()-started
    (ROOT/'results/audit.json').write_text(json.dumps(data,indent=2)+'\n')
    (ROOT/'results/geometric_histories.json').write_text(json.dumps(meshes,indent=2)+'\n')
    (ROOT/'examples/transported_solid_tori.json').write_text(json.dumps(retained,indent=2)+'\n')
    # A complete delivered example with all stratum proofs.
    m=interval_model(12);answer=optimize_band(m,2)
    (ROOT/'examples/interval_band.json').write_text(json.dumps({'model':m.to_dict(),'answer':answer},indent=2)+'\n')
    g=product_solid_torus();m=g.model();answer=optimize_band(m,2)
    (ROOT/'examples/solid_torus_band.json').write_text(json.dumps({'geometry':g.to_dict(),'model':m.to_dict(),'answer':answer},indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':run()
