#!/usr/bin/env python3
"""Replay the 255-state prefilled-negation control without a ProveIt checkout.

Python 3.10+ standard library only. This verifies pinned-source extraction,
the exact optimized-tree replacement, six complete affine fold replays, and
the literal 82,552-step blank prefix. It does not claim a new proof-assistant
consistency endpoint or a machine with fewer than 252 working states.

The affine checker invokes four attributed register-Box contracts. Its
unbounded interpretation is conditional on those contracts and the declared
tape-frame hypotheses; it is not a finite register-value test.
"""
from __future__ import annotations
import argparse, gzip, hashlib, importlib.util, json, re, sys, time
from collections import Counter
from functools import cache
from pathlib import Path
from types import SimpleNamespace

import verify as source_control
from macro_signatures import make_signature

HERE=Path(__file__).resolve().parent
PHYSICAL=(6,2,0,4,3,7,8,5,1)
BOX_STATES={0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
BOX_PAIRS={(str(q),b) for q in BOX_STATES for b in (0,1)}-{('3',0)}
FOLDS=((61,301),(302,45),(303,32),(177,203),(213,134),(237,0))
PINNED={
 'data/reference252.tm':'939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713',
 'data/optimized_original203.json':'9bcbe8c5927b28268f227ed1e40def5a13093928c8edb2b2c6cd89e6ae8df33b',
 'data/optimized_output_prefill2.json':'dbbefd67b689a77ab43dddcbb9da969a852352346b5afc2c5db2bb0165a25dfc',
 'prepared_runtime/prefill261.tm':'65ad4a3a321e76ed32dd2fd44d3e741df0fb240487f6c559579a403705fe15ea',
 'prepared_runtime/prefill255.tm':'463067a5a42476c8efeacb296d83df69b7366b0d1894a4e11f418840e79fb0fb',
 'vendor/strict_affine.py':'da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce',
 'macro_signatures.py':'8a69acc6dd7e64bdc01ebcd167ed3e41c33d88b0678674e8a322c859cdfdb054',
}
PROG_SHA='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def digest(raw):return hashlib.sha256(raw).hexdigest()

def load_dag(path):
    data=json.loads(path.read_text())
    nodes={int(q):tuple(tuple(e) for e in pair) for q,pair in data['nodes'].items()}
    assert all(len(pair)==2 for pair in nodes.values())
    return nodes,data['root']

def unfold(nodes,root):
    @cache
    def visit(edge):
        return ('N',*(visit(e) for e in nodes[edge[1]])) if edge[0]=='N' else edge
    return visit(('N',root))

def source_tree_check():
    native,_=source_control.load_source()
    def native_edge(e):
        k,*v=e.split()
        return ('H',) if k=='EHalt' else ({'ENode':'N','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C'}[k],int(v[0]))
    native={q:tuple(native_edge(e) for e in pair) for q,pair in native.items()}
    raw=gzip.decompress((HERE/'data/Prog254.v.gz').read_bytes())
    assert digest(raw)==PROG_SHA
    body=raw.decode().split('Definition p254_tab : list (cedge * cedge) := [',1)[1].split('].',1)[0]
    def compiled_edge(e):
        k,*v=e.split();return ('H',) if k=='CH' else (k[1:],int(v[0]))
    source={i:tuple(compiled_edge(e) for e in pair) for i,pair in enumerate(re.findall(r'\(([^,]+), ([^)]+)\)',body))}
    assert len(source)==6459
    original,root=load_dag(HERE/'data/optimized_original203.json')
    changed,changed_root=load_dag(HERE/'data/optimized_output_prefill2.json')
    assert len(original)==len(changed)==203
    oldtree=unfold(original,root)
    assert oldtree==unfold(source,0)
    targets={q:make_signature(unfold(native,q)) for q in (218,120)}
    matches={q:[] for q in targets}
    for node in original:
        try:signature=make_signature(unfold(original,node))
        except ValueError:continue  # The candidate subtree has an external control exit.
        for q,expected in targets.items():
            if signature==expected:matches[q].append(node)
    assert matches=={218:[92],120:[56]}
    old_wn=unfold(original,92)
    replacement=('N',('N',('I',7),('I',7)),unfold(original,56))
    replaced=0
    def replace(e):
        nonlocal replaced
        if e==old_wn:replaced+=1;return replacement
        return ('N',replace(e[1]),replace(e[2])) if e[0]=='N' else e
    assert replace(oldtree)==unfold(changed,changed_root)
    assert replaced==30
    return changed,changed_root,dict(pinned_Prog254_sha256=PROG_SHA,
        original_literal_nodes=6459,original_shared_nodes=203,changed_shared_nodes=203,
        operation_signature_matches=matches,replaced_negation_occurrences=replaced,
        frozen_changed_tree_reproduced_exactly=True,
        signature_scope='Increment-block commutation with both named decrement outcomes retained; no new proof-assistant theorem.')

def read_table(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=q,int(b)
        assert key not in rows
        rows[key]=int(w),d,t
    states={q for q,b in rows}
    assert set(rows)=={(q,b) for q in states for b in (0,1)}
    assert '254' not in states
    assert all(w in (0,1) and d in ('L','R') and t in states|{'254'} for w,d,t in rows.values())
    return rows

def encode(table):
    return ('#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items(),key=lambda row:(int(row[0][0]),row[0][1])))).encode()

def increment(p):
    i=p.rfind('0')
    return p[:i]+'1' if i>=0 else None

def strip(p,bit,n):
    i=len(p)
    while n and i:i-=1;n-=p[i]==bit
    return p[:i]

def sites(nodes,root):
    todo=[(('N',root),'')]
    while todo:
        edge,p=todo.pop();op=edge[0]
        if op=='N':
            a,b=nodes[edge[1]];todo.extend(((b,p+'1'),(a,p+'0')))
        else:yield p,op,None if op=='H' else edge[1]

def cases_for(strict,nodes,root):
    cases=[];counts=Counter()
    for p,op,r in sites(nodes,root):
        counts[op]+=1
        for zero in (True,False) if op=='D' else (None,):
            physical=PHYSICAL[r] if op in ('I','D') else r
            branch=(physical,zero) if op=='D' else None
            if op=='I' or op=='D' and not zero:nxt=increment(p)
            elif op=='D':nxt=increment(strip(p,'0',1))
            elif op=='B':nxt=increment(strip(p,'0',r))
            elif op=='C':nxt=strip(p,'1',r)
            else:nxt=''
            effect=('inc',physical) if op=='I' else ('dec',physical) if op=='D' and not zero else None
            right=[('b',int(c)) for c in (nxt or '')]+[('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
            cases.append((p,op,branch,strict.canon([('b',1)],right)))
    assert sum(counts.values())==5590 and counts['D']==1631 and len(cases)==7221
    return cases,dict(counts)

def check_cases(strict,table,cases):
    minimum=10**9;totals=Counter()
    for i,(p,op,branch,target) in enumerate(cases):
        try:counts,literal=strict.run(table,p,branch,target,halt=op=='H',fuel=1500)
        except (KeyError,AssertionError) as exc:raise AssertionError(('affine case failed',i,p,op,branch,str(exc))) from exc
        assert literal>0
        minimum=min(minimum,literal);totals.update(counts)
    return dict(cases=len(cases),minimum_literal_steps=minimum,rule_totals=dict(totals))

def blank_prefix(table):
    q='64';head=0;ones=set()
    for _ in range(82552):
        w,d,q=table[q,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=1 if d=='R' else -1
    return q,head,tuple(sorted(ones))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='Save the JSON result here.')
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions required; do not use -O or -OO.')
    start=time.monotonic()
    for path,h in PINNED.items():assert digest((HERE/path).read_bytes())==h,('changed pinned input',path)
    nodes,root,derivation=source_tree_check()
    # The unchanged upstream file imports cost_search only for its unused audit
    # and main entry points. Supply an inert name to load run/canon/oracle. No
    # upstream driver is executed, and no repository path is probed.
    sys.modules['cost_search']=SimpleNamespace()
    spec=importlib.util.spec_from_file_location('attributed_strict_affine',HERE/'vendor/strict_affine.py')
    strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
    cases,leaf_kinds=cases_for(strict,nodes,root)
    reference=read_table(HERE/'data/reference252.tm')
    table=read_table(HERE/'prepared_runtime/prefill261.tm')
    assert len(table)==522 and len(BOX_PAIRS)==55
    assert all(table[k]==reference[k] for k in BOX_PAIRS)
    results=[dict(states=261,table_sha256=digest(encode(table)),**check_cases(strict,table,cases))]
    for dead,target in FOLDS:
        dead,target=str(dead),str(target)
        assert all(k[0]!=dead and table[k][2]!=dead for k in BOX_PAIRS)
        table={k:(w,d,target if t==dead else t) for k,(w,d,t) in table.items() if k[0]!=dead}
        assert all(table[k]==reference[k] for k in BOX_PAIRS)
        results.append(dict(states=len(table)//2,fold=[int(dead),int(target)],table_sha256=digest(encode(table)),**check_cases(strict,table,cases)))
    frozen=(HERE/'prepared_runtime/prefill255.tm').read_bytes()
    assert encode(table)==frozen and len(table)==510
    root_frame=blank_prefix(reference)
    assert root_frame==blank_prefix(table)
    assert root_frame[0:2]==('96',2) and len(root_frame[2])==77
    # Explicit negative controls for oracle guards, effect reuse, and a row.
    assert strict.oracle('43',None,('mark',0)) is None
    assert strict.oracle('43',(1,True),('mark',0)) is None
    assert strict.oracle('64',None,('plain',('inc',0))) is None
    bad=table.copy();bad['96',0]=(0,'R','254')
    try:check_cases(strict,bad,cases[:1])
    except (AssertionError,KeyError):pass
    else:raise AssertionError('damaged decoder row was accepted')
    answer=dict(status='PASS',scope=__doc__,input_sha256=PINNED,source_derivation=derivation,
        source_leaf_kinds=leaf_kinds,affine_cases_per_table=7221,protected_Box_rows=55,
        physical_order=['W','L','T','D','A','Y','N','H','X'],fold_replay=results,
        final_working_states=255,total_rows=510,halt_state=254,start_state=64,dispatch_state=96,
        blank_prefix=dict(steps=82552,state=96,head=2,one_cells=list(root_frame[2]),matches_reference252_exactly=True),
        negative_controls=dict(unguarded_decrement=True,wrong_register_guard=True,second_effect_on_box=True,damaged_decoder_row=True),
        binary_consistency_endpoint_proved=False,smaller_than252_machine_claimed=False,
        elapsed_seconds=time.monotonic()-start)
    if args.output:args.output.write_text(json.dumps(answer,indent=2)+'\n')
    print(json.dumps(answer,indent=2))

if __name__=='__main__':main()
