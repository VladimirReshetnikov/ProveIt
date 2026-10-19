#!/usr/bin/env python3
"""Literal binary Mealy-oracle encoding of all trusted C254 templates.

An architecture component, NOT a complete consistency-search Turing machine.
One working state per shared constructor plus an eleven-state leaf-code emitter.
Every transition writes a bit and moves R. HALT is separate.

The path verifier checks all leaves, whose prefixes form a finite full binary
prefix code. On traversing edge b of a tag t constructor, the oracle writes bit
(t >> b) & 1, then enters that child. Both outgoing edges of every occurrence
are checked across the leaf paths; hence both bits of every tag are checked.
"""
from __future__ import annotations

if not __debug__:
    raise RuntimeError('Assertions must be enabled; do not use python -O.')

import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1] / 'source'
CERT = ROOT/'Computability/BusyBeaver/Research/ZFC/term-certificates'
SPEC = ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/50-terms-data-spec254.json'
EXPECTED_SPEC_HASH = 'fbce2fd79f909cce5b6d0ca52e2c7ead86ce052285294cb7c9dffa657a217adc'

def load_source():
    assert hashlib.sha256(SPEC.read_bytes()).hexdigest() == EXPECTED_SPEC_HASH
    sys.path.insert(0, str(CERT))
    import term_circuits as C
    import term_patterns as P
    return C, P, C.load_templates(SPEC)


def unroll(t, i):
    if i < t.arity: return ('p', i)
    if i == t.arity: return ('z',)
    tag, l, r = t.steps[i-t.arity-1]
    return (tag, unroll(t,l), unroll(t,r))


def constructor_set(roots):
    seen = set()
    def visit(t):
        if t[0] in ('p','z') or t in seen: return
        visit(t[1]); visit(t[2]); seen.add(t)
    for t in roots.values(): visit(t)
    return seen


def structural_key(t):
    return repr(t)


def compile_oracle(templates):
    roots = {k:unroll(t,t.root) for k,t in templates.items()}
    nodes = sorted(constructor_set(roots), key=structural_key)
    ids = {t:i for i,t in enumerate(nodes)}
    # Literal three-bit output: 000=Z, 001=P0, 010=P1, 011=P2, 100=P3.
    codes = {('z',):'000', **{('p',i):format(i+1,'03b') for i in range(4)}}
    suffixes = sorted({code[i:] for code in codes.values() for i in range(3)},
                      key=lambda s:(-len(s),s))
    emit_ids = {s:len(nodes)+i for i,s in enumerate(suffixes)}
    halt = len(nodes)+len(suffixes)
    def target(t):
        return emit_ids[codes[t]] if t[0] in ('p','z') else ids[t]
    table = {}
    for t,q in ids.items():
        for b in range(2): table[q,b] = ((t[0]>>b)&1, 'R', target(t[1+b]))
    for s,q in emit_ids.items():
        for b in range(2): table[q,b] = (int(s[0]), 'R', emit_ids[s[1:]] if len(s)>1 else halt)
    return {'table':table,'halt':halt,'roots':{k:ids[v] for k,v in roots.items()},
            'constructors':len(nodes),'emitters':len(suffixes),'syntax':roots,
            'nodes':nodes}


def run_oracle(o, rule, path):
    # A prepared-path component run; tape is binary and otherwise blank.
    tape = {i:b for i,b in enumerate(path) if b}
    q=o['roots'][rule]; head=0; trace=[]
    while q!=o['halt']:
        read=tape.get(head,0)
        w,d,q2=o['table'][q,read]
        assert d=='R'
        if w:tape[head]=w
        else:tape.pop(head,None)
        trace.append((q,read,w,q2))
        q=q2; head+=1
        assert head<=26
    result=[tape.get(i,0) for i in range(head)]
    leafcode=int(''.join(map(str,result[-3:])),2)
    assert 0<=leafcode<=4
    return result[:-3], leafcode, trace


def enumerate_leaf_paths(o,rule):
    """No trusted precomputed path list: start zero and increment used prefix.

    Leaf prefixes exhaust lexicographic order. A full binary tree's leftmost
    remaining leaf extends p with zeros; incrementing the returned path skips
    exactly the completed leaf's padded extensions.
    """
    prefix=[]
    while True:
        observed, leaf, trace=run_oracle(o,rule,prefix)
        path=[step[1] for step in trace[:-3]]
        assert path[:len(prefix)]==prefix
        yield path,observed,leaf
        i=len(path)-1
        while i>=0 and path[i]==1: i-=1
        if i<0:break
        prefix=path[:i]+[1]


def match_oracle(nodes,out,args,o,rule,stats=None):
    """Exact fixed pattern verifier, no numeric Cantor arithmetic.

    Input arena validity is a separate prerequisite, as in the original
    match_pattern function. This function tests actual node IDs at leaves.
    """
    if stats is None: stats={}
    stats.update(queries=0,oracle_steps=0,actual_edges=0)
    for path,expected,leaf in enumerate_leaf_paths(o,rule):
        stats['queries']+=1; stats['oracle_steps']+=len(path)+3
        actual=out; observed=[]
        for b in path:
            stats['actual_edges']+=1
            if actual==0:
                tag,l,r=0,0,0
            else:
                _,tag,l,r=nodes[actual]
            observed.append((tag>>b)&1)
            actual=(l,r)[b]
        if observed!=expected: return False
        wanted=0 if leaf==0 else args[leaf-1]
        if actual!=wanted:return False
    return True


def make_instance(t,args,nodes,intern,duplicates=False,rng=None):
    if t[0]=='z':return 0
    if t[0]=='p':return args[t[1]]
    l=make_instance(t[1],args,nodes,intern,duplicates,rng)
    r=make_instance(t[2],args,nodes,intern,duplicates,rng)
    tag=t[0]
    if tag==0 and l==r==0:return 0
    key=(tag,l,r)
    if not duplicates and key in intern:return intern[key]
    out=len(nodes); nodes.append(['b',tag,l,r]);intern[key]=out;return out


def canonical_start_arena():
    return [['z'],['b',1,0,0],['b',2,0,0],['b',3,0,0]]


def legacy_match(P,nodes,out,args,t):
    stats={key:0 for key in ['max_pending_obligations','pattern_visits',
            'parameter_checks','literal_zero_checks','pattern_constructor_checks',
            'virtual_zero_constructors']}
    return P.match_pattern(nodes,out,args,t,stats)


def blank_probe_table(o,rule,path):
    """Complete binary blank-tape table for ONE oracle probe, not proof search.

    Reverse writer writes the chosen path while moving L, then one adapter
    moves R into the chosen root. Every writer/adapter state is charged.
    Output includes every oracle state, including states not reachable for
    this one probe. No prepared tape is given free in this demonstration.
    """
    table=dict(o['table']); nextid=o['halt']
    # The old component halt is reidentified AFTER adding writer states.
    writer_ids=list(range(nextid,nextid+len(path)))
    adapter=nextid+len(path); halt=adapter+1
    table={key:(w,d,halt if q==o['halt'] else q) for key,(w,d,q) in table.items()}
    for j,(q,b) in enumerate(zip(writer_ids,reversed(path))):
        target=writer_ids[j+1] if j+1<len(writer_ids) else adapter
        for read in range(2):table[q,read]=(b,'L',target)
    for read in range(2):table[adapter,read]=(read,'R',o['roots'][rule])
    return table,writer_ids[0] if writer_ids else adapter,halt


def simulate(table,start,halt,limit=1000):
    tape={};q=start;h=0;steps=0
    while q!=halt:
        if steps>=limit:raise RuntimeError('fuel exhausted')
        w,d,q=table[q,tape.get(h,0)]
        if w:tape[h]=w
        else:tape.pop(h,None)
        h+=1 if d=='R' else -1;steps+=1
    return tape,h,steps


def save_table(path,table,halt,start):
    lines=[f'# working_states={halt}; start={start}; halt={halt}',
           '# q read write move next']
    assert set(q for q,b in table)==set(range(halt))
    assert len(table)==2*halt
    for (q,b),(w,d,n) in sorted(table.items()):lines.append(f'{q} {b} {w} {d} {n}')
    path.write_text('\n'.join(lines)+'\n')


def tests(o,templates,C,P):
    results={'positive_template_assignments':0,'random_arena_comparisons':0,
             'mutated_instance_comparisons':0,'blank_probes':0,'queried_leaf_paths':0}
    details={}
    for rule,t in templates.items():
        paths=list(enumerate_leaf_paths(o,rule))
        pbits=[tuple(p) for p,e,l in paths]
        assert len(pbits)==len(set(pbits))
        assert all(not (len(a)<len(b) and b[:len(a)]==a) for a in pbits for b in pbits)
        depth=max(map(len,pbits))
        assert sum(1<<(depth-len(p)) for p in pbits)==1<<depth
        details[rule]={'local_circuit_gates':len(t.steps),'leaves':len(paths),
                       'maximum_depth':depth,'path_edges':sum(len(p) for p,e,l in paths),
                       'oracle_transitions':sum(len(p)+3 for p,e,l in paths)}
        for p,e,leaf in paths:
            table,start,halt=blank_probe_table(o,rule,p)
            tape,head,steps=simulate(table,start,halt)
            origin=1-len(p)
            actual=[tape.get(origin+i,0) for i in range(len(e)+3)]
            assert actual==e+list(map(int,format(leaf,'03b')))
            assert head==origin+len(e)+3
            assert steps==len(p)+1+len(e)+3
            results['blank_probes']+=1
        results['queried_leaf_paths']+=len(paths)
        for args in itertools.product(range(3),repeat=t.arity):
            nodes=canonical_start_arena(); intern={tuple(n[1:]):i for i,n in enumerate(nodes) if i}
            out=make_instance(o['syntax'][rule],args,nodes,intern)
            assert legacy_match(P,nodes,out,args,t)
            assert match_oracle(nodes,out,args,o,rule)
            results['positive_template_assignments']+=1
            # Valid local tag changes; skip zero aliases and compare exact acceptances.
            for index in range(1,len(nodes)):
                old=nodes[index][1]
                new=(old+1)%4
                if new==0 and nodes[index][2:]==[0,0]:continue
                nodes[index][1]=new
                expected=legacy_match(P,nodes,out,args,t)
                observed=match_oracle(nodes,out,args,o,rule)
                assert observed==expected,(rule,args,index,observed,expected)
                nodes[index][1]=old
                results['mutated_instance_comparisons']+=1
    rng=random.Random(157246)
    for trial in range(1500):
        nodes=[['z']]
        for i in range(1,rng.randrange(2,40)):
            tag,l,r=rng.randrange(4),rng.randrange(i),rng.randrange(i)
            if (tag,l,r)==(0,0,0):tag=1
            nodes.append(['b',tag,l,r])
        for rule,t in templates.items():
            args=[rng.randrange(len(nodes)) for i in range(t.arity)]
            out=rng.randrange(len(nodes))
            assert match_oracle(nodes,out,args,o,rule)==legacy_match(P,nodes,out,args,t)
            results['random_arena_comparisons']+=1
    results['templates']=details
    return results


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=Path(__file__).parent)
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
    C,P,templates=load_source();o=compile_oracle(templates)
    result=tests(o,templates,C,P)
    result.update(scope='Binary template-oracle component and high-level exact matcher; not a full search TM.',
        source_spec_sha256=EXPECTED_SPEC_HASH,constructor_states=o['constructors'],
        leaf_emitter_states=o['emitters'],working_states=o['halt'],transition_rows=len(o['table']),
        separate_halt=o['halt'],entry_states=o['roots'])
    # Component table is complete, but requires a prepared path and a selected entry.
    save_table(args.output/'template_oracle_102.tm',o['table'],o['halt'],o['roots'][11])
    paths=list(enumerate_leaf_paths(o,11));longest=max(paths,key=lambda x:len(x[0]))[0]
    table,start,halt=blank_probe_table(o,11,longest)
    save_table(args.output/'blank_longest_bundle_probe_126.tm',table,halt,start)
    result['blank_longest_bundle_probe']={'working_states':halt,'start':start,
      'halt':halt,'path':longest,'steps':simulate(table,start,halt)[2],
      'purpose':'Explicitly charged blank-tape oracle demonstration; always halts.'}
    for name in ['template_oracle_102.tm','blank_longest_bundle_probe_126.tm']:
        result[name+'_sha256']=hashlib.sha256((args.output/name).read_bytes()).hexdigest()
    (args.output/'pattern_oracle_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
