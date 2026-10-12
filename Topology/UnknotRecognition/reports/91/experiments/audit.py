#!/usr/bin/env python3
"""Deterministic correctness audit; no network, no upstream knot package required."""
from __future__ import annotations
import json, math, platform, random, time, hashlib
from itertools import combinations
from pathlib import Path
from sparse_cuts import (solve, connected_support_bound, support_bound, circular_ladder,
                         thue_morse, witness_dag, cut_addresses, mark_address)
from checker import verify_certificate, verify_addresses, metadata
from reference import expand, brute_signature

ROOT=Path(__file__).resolve().parents[1]


def source_hashes():
    paths=sorted((ROOT/"src").glob("*.py"))+sorted((ROOT/"experiments").glob("*.py"))+sorted((ROOT/"tests").glob("*.py"))
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

def leaf(n, es, ts=None):
    node={"kind":"leaf","vertices":n,"edges":[list(e) if len(e)==3 else [*e,1] for e in es],
          "terminals":list(range(n)) if ts is None else list(ts)}
    named=set(node["terminals"])|{v for e in node["edges"] for v in e[:2]}
    isolated=sorted(set(range(n))-named)
    if isolated and n>1: node["isolated_vertices"]=isolated
    return node

def grammar(n): return {"schema":"proveit.graph-grammar.v1","nodes":n}

def connected(n, es):
    seen={0}
    while True:
        old=len(seen)
        for u,v,*_ in es:
            if u in seen or v in seen: seen.update((u,v))
        if len(seen)==old: return len(seen)==n

def project(response, ts):
    out={}
    for (mask,flags), cost in response.items():
        key=(sum(((mask>>t)&1)<<i for i,t in enumerate(ts)),flags)
        out[key]=min(cost,out.get(key,10**9))
    return out

def star_pair(a):
    return grammar([leaf(a+1,[(0,v) for v in range(1,a+1)]),
        {"kind":"join","left":0,"right":0,"left_map":list(range(a+1)),
         "right_map":[0]+list(range(a+1,2*a+1)),"terminals":list(range(2*a+1))}])

def random_grammar(rng):
    nodes=[]
    for _ in range(2):
        n=rng.randint(1,4)
        es=[(rng.randrange(n),rng.randrange(n),rng.randint(1,4)) for _ in range(rng.randrange(7))]
        nodes.append(leaf(n,es,rng.sample(range(n),rng.randrange(n+1))))
    for i in range(2,rng.randint(4,8)):
        cs=[rng.randrange(i)] if rng.random()<0.25 else [rng.randrange(i),rng.randrange(i)]
        lens=[len(nodes[c]["terminals"]) for c in cs]
        total=sum(lens)
        raw=[rng.randrange(max(1,total)) for _ in range(total)]
        canon={}; labels=[canon.setdefault(v,len(canon)) for v in raw]
        q=len(canon); ts=rng.sample(range(q),rng.randrange(q+1))
        if len(cs)==1:
            nodes.append({"kind":"map","child":cs[0],"mapping":labels,"terminals":ts})
        else:
            nodes.append({"kind":"join","left":cs[0],"right":cs[1],
                          "left_map":labels[:lens[0]],"right_map":labels[lens[0]:],"terminals":ts})
    return grammar(nodes)

def main():
    start=time.perf_counter(); counts={}; projections=0; leaf_cases=0; checker_cases=0
    for n in range(1,6):
        pairs=list(combinations(range(n),2)); counts[n]=0
        for mask in range(1<<len(pairs)):
            es=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
            if not connected(n,es): continue
            counts[n]+=1
            g=grammar([leaf(n,es)])
            for k in range(4):
                result=solve(g,k); direct=brute_signature(expand(g),k)
                assert result.response()==direct
                leaf_cases+=1
                for tmask in range(1<<n):
                    ts=[i for i in range(n) if tmask>>i&1]
                    p=project(result.response(),ts)
                    assert p==project(direct,ts)
                    assert len({m for m,f in p})<=connected_support_bound(len(ts),k)
                    projections+=1
                if k==3:
                    assert verify_certificate(g,result.certificate())["verified"]
                    checker_cases+=1
    rng=random.Random(20261012)
    random_leaves=1000
    for _ in range(random_leaves):
        n=rng.randint(1,9)
        es=[(rng.randrange(n),rng.randrange(n),rng.randint(1,8)) for _ in range(rng.randrange(18))]
        g=grammar([leaf(n,es,rng.sample(range(n),rng.randrange(n+1)))])
        k=rng.randrange(4); r=solve(g,k)
        assert r.response()==brute_signature(expand(g),k)
        assert [m.record() for m in r.metadata]==metadata(g)
        assert verify_certificate(g,r.certificate())["verified"]
        checker_cases+=1
    accepted=attempts=0; max_expanded=0; join_nodes=0; pair_checks=0
    while accepted<1500:
        attempts+=1; g=random_grammar(rng)
        try: literal=expand(g,12,60)
        except ValueError: continue
        k=rng.randrange(4); r=solve(g,k)
        assert r.response()==brute_signature(literal,k)
        assert [m.record() for m in r.metadata]==metadata(g)
        assert verify_certificate(g,r.certificate())["verified"]
        for node in g["nodes"]:
            if node["kind"]!="join": continue
            a,b=node["left"],node["right"]
            ra,rb=len(g["nodes"][a]["terminals"]),len(g["nodes"][b]["terminals"])
            ca,cb=r.metadata[a].terminal_components,r.metadata[b].terminal_components
            # Conservative skeleton lengths; the proof gives a smaller exact bound.
            d=2*(ra+rb)
            bound=16*(1<<(ca+cb))*sum(math.comb(d,j) for j in range(min(k,d)+1))
            candidates=sum(e.cost+f.cost<=k for e in r.tables[a].values() for f in r.tables[b].values())
            assert candidates<=bound
            pair_checks+=1
        join_nodes+=sum(n["kind"]=="join" for n in g["nodes"])
        checker_cases+=1; accepted+=1
        max_expanded=max(max_expanded,literal["vertices"])
    sharp=[]
    for a in range(3,13):
        r=solve(star_pair(a),3)
        expected=2*sum(math.comb(2*a,j) for j in range(4))
        assert len(r.response())==expected
        # With all vertices terminal a state fixes its entire coloring.
        sharp.append({"arms_per_child":a,"root_states":len(r.response()),"sharp_formula":expected})
    stress=[]
    examples={"ladder_2pow256":circular_ladder(1<<256),"thue_morse_128":thue_morse(128)}
    hidden=grammar([leaf(2,[(0,1)],[])])
    for i in range(128):
        hidden["nodes"].append({"kind":"join","left":i,"right":i,"left_map":[],"right_map":[],"terminals":[]})
    examples["hidden_components_2pow128"]=hidden
    examples["triangular_prism"]=circular_ladder(3)
    examples["k4"]=grammar([leaf(4,list(combinations(range(4),2)),[])])
    for name,g in examples.items():
        r=solve(g); cert=r.certificate()
        assert verify_certificate(g,cert)["verified"]
        checker_cases+=1
        (ROOT/"examples"/(name+".json")).write_text(json.dumps(g,indent=2)+"\n")
        (ROOT/"data"/(name+".certificate.json")).write_text(json.dumps(cert,separators=(",",":"))+"\n")
        row={"name":name,"rules":len(g["nodes"]),"peak_states":max(map(len,r.tables)),
             "total_states":sum(map(len,r.tables)),"operations":r.operations,
             "has_marked_cut":r.has_marked_cut(),"root_metadata":r.metadata[r.root].record()}
        if r.has_marked_cut():
            w=witness_dag(r); cuts=cut_addresses(r); marks=[mark_address(r,c) for c in (0,1)]
            assert verify_addresses(g,w,cuts,marks)["verified"]
            pack={"witness":w,"cut_addresses":cuts,"mark_addresses":marks}
            (ROOT/"data"/(name+".witness.json")).write_text(json.dumps(pack,separators=(",",":"))+"\n")
            row.update(witness_records=len(w["records"]),cut_edges=len(cuts),
                       longest_cut_address=max((len(c["path"]) for c in cuts),default=0))
        stress.append(row)
    summary={"source_sha256":source_hashes(),"seed":20261012,"python":platform.python_version(),"platform":platform.platform(),
             "connected_simple_graphs_by_vertices":counts,"connected_graphs":sum(counts.values()),
             "connected_graph_threshold_cases":leaf_cases,"terminal_subset_projections":projections,
             "random_weighted_leaves":random_leaves,"random_grammars_accepted":accepted,
             "random_grammar_attempts":attempts,"max_literal_vertices":max_expanded,
             "random_join_pair_bound_checks":pair_checks,"complete_certificate_replays":checker_cases,
             "sharp_star_pairs":sharp,"stress":stress,"elapsed_seconds":time.perf_counter()-start}
    (ROOT/"data/audit.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps(summary,indent=2))

if __name__=="__main__": main()
