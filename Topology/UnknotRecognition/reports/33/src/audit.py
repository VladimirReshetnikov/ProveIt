"""Deterministic exhaustive and randomized audits; outputs machine-readable data."""
from __future__ import annotations
import argparse,itertools,json,math,platform,random,time
from pathlib import Path
from abstract_models import BooleanSystem,Rule,brute_endpoints
from layered_search import layered_traces,normal_form,ancestor_cone,find_layered
from dart_kernel import *
from verify_certificate import serialize,verify

ROOT=Path(__file__).resolve().parents[1]

def boolean_audit():
    rules=[]
    for bit in range(3):
        other=[i for i in range(3) if i!=bit]
        for options in itertools.product((-1,0,1),repeat=2):
            guard=sum(1<<i for i,v in zip(other,options) if v>=0)
            value=sum(1<<i for i,v in zip(other,options) if v==1)
            rules.append(Rule(1<<bit,guard,value))
    comparisons=systems=traces=0
    for size in (1,2,3):
        for selected in itertools.combinations(rules,size):
            systems+=1; system=BooleanSystem(selected)
            for initial in range(8):
                for births in range(1,4):
                    expected,t=brute_endpoints(system,initial,4,births); traces+=t
                    actual={initial}|{x for x,_ in layered_traces(system,initial,4,max_roots=births)}
                    assert actual==expected,(selected,initial,births,actual,expected)
                    comparisons+=1
    return dict(systems=systems,comparisons=comparisons,reference_traces=traces,
                depth=4,discrepancies=0)

def forest_audit():
    comparisons=0
    # Coefficients by convolution of T=z(1+T)^d, independent of Lagrange inversion.
    def mul(a,b,K):
        out=[0]*(K+1)
        for i,x in enumerate(a):
            for j,y in enumerate(b[:K+1-i]): out[i+j]+=x*y
        return out
    K=18
    for d in range(1,8):
        t=[0]*(K+1)
        for _ in range(K):
            base=t.copy();base[0]+=1;p=[1]+[0]*K
            for __ in range(d): p=mul(p,base,K)
            t=[0]+p[:-1]
        p=[1]+[0]*K
        for b in range(1,7):
            p=mul(p,t,K)
            for k in range(b,K+1):
                expected=b*math.comb(d*k,k-b)//k
                assert p[k]==expected,(d,b,k,p[k],expected)
                comparisons+=1
    return dict(comparisons=comparisons,discrepancies=0)

def connected(adj,S):
    if not S: return False
    seen={min(S)};todo=list(seen)
    while todo:
        u=todo.pop()
        for v in (set(adj[u])&set(S))-seen: seen.add(v);todo.append(v)
    return seen==set(S)

def diagram_audit(attempts=1200):
    rng=random.Random(8102601); sys=R3System()
    count=endpoints=action_checks=pairs=cone_checks=nonempty_cones=0
    max_footprint=max_vertices=max_incidence=max_successors=0; saved=[]
    for attempt in range(attempts):
        strands=rng.randrange(3,7); length=rng.randrange(8,33)
        word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(length)]
        try: initial=from_braid(strands,word)
        except ValueError: continue
        count+=1
        state,_=reduce_12(initial)
        if state.n<3: continue
        graph=projection_graph(state); actions=list(sys.actions(state))
        incidence={d:0 for d in range(len(state.alpha))}
        for a in actions:
            action_checks+=1; out=sys.apply(state,a);out.validate()
            F=a.footprint; V={d//4 for d in F}
            assert len(F)<=18 and len(V)<=9 and connected(graph,V)
            assert {state.alpha[d] for d in F}==set(F)=={out.alpha[d] for d in F}
            assert all(state.alpha[d]==out.alpha[d] for d in range(len(state.alpha)) if d not in F)
            inverse=tuple(sorted(d^2 for d in a.payload))
            inv=next(b for b in sys.actions(out) if b.key==inverse)
            assert sys.apply(out,inv)==state
            successors=sum(not a.footprint.isdisjoint(b.footprint) for b in sys.actions(out))
            assert successors<=36
            max_successors=max(max_successors,successors)
            max_footprint=max(max_footprint,len(F));max_vertices=max(max_vertices,len(V))
            for d in F: incidence[d]+=1
        if incidence:
            assert max(incidence.values())<=8
            max_incidence=max(max_incidence,max(incidence.values()))
        for a,b in itertools.combinations(actions,2):
            if a.footprint.isdisjoint(b.footprint):
                assert sys.apply(sys.apply(state,a),b)==sys.apply(sys.apply(state,b),a);pairs+=1
        # All endpoints, not only positive witnesses; independent sequential oracle.
        if endpoints<180 and len(actions)<=8:
            for births in (1,2,3):
                expected,_=brute_endpoints(sys,state,3,births)
                actual={state}|{x for x,_ in layered_traces(sys,state,3,max_roots=births)}
                assert actual==expected
                endpoints+=1
        start=state; trace=[]
        for _ in range(8):
            available=list(sys.actions(state))
            if not available: break
            a=rng.choice(available);trace.append(a);state=sys.apply(state,a)
            for terminal in list(reductions(state))[:2]:
                F=footprint(state,terminal[1]);kept,union=ancestor_cone(trace,F)
                S={d//4 for d in union}
                assert len(S)<=7*len(kept)+6
                graph0=projection_graph(start)
                assert connected(graph0,S)
                C={d//4 for d in terminal[1]}
                for retained in kept: C.update(d//4 for d in retained.key)
                assert len(C)<=3*len(kept)+2
                assert connected(graph0,C)
                neighborhood=C|{v for c in C for v in graph0[c]}
                assert S==neighborhood
                assert union==footprint(start,tuple(4*c for c in C))
                replay=start
                for retained in kept: replay=sys.apply(replay,retained)
                assert terminal in list(reductions(replay))
                layers=normal_form(kept); layer_replay=start
                for layer in layers:
                    for retained in layer: layer_replay=sys.apply(layer_replay,retained)
                assert layer_replay==replay
                cone_checks+=1;nonempty_cones+=bool(kept)
                if kept and len(saved)<10:
                    from layered_search import Witness
                    cert=serialize(start,Witness(layers,terminal,replay),len(kept))
                    assert verify(cert)["verified"];saved.append(cert)
    for i,cert in enumerate(saved):
        (ROOT/"artifacts"/f"witness_{i:02d}.json").write_text(json.dumps(cert,indent=2)+"\n")
    return dict(seed=8102601,attempts=attempts,validated_knots=count,
        bounded_endpoint_comparisons=endpoints,action_checks=action_checks,
        commuting_pair_checks=pairs,cone_checks=cone_checks,nonempty_cones=nonempty_cones,
        max_dart_footprint=max_footprint,max_crossing_support=max_vertices,
        max_site_incidence=max_incidence,max_successors_per_parent=max_successors,
        saved_certificates=len(saved),core_cone_checks=cone_checks,
        initial_star_equality_checks=cone_checks,discrepancies=0)

def main():
    p=argparse.ArgumentParser();p.add_argument("--skip-boolean",action="store_true");args=p.parse_args()
    start=time.perf_counter();out={"python":platform.python_version(),"scope":"research kernels only"}
    if not args.skip_boolean:
        out["boolean"]=boolean_audit();print("boolean",out["boolean"],flush=True)
    out["forests"]=forest_audit();print("forests",out["forests"],flush=True)
    out["diagrams"]=diagram_audit();print("diagrams",out["diagrams"],flush=True)
    out["elapsed_seconds"]=time.perf_counter()-start
    (ROOT/"data"/"audit.json").write_text(json.dumps(out,indent=2)+"\n")
if __name__=="__main__":main()
