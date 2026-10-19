#!/usr/bin/env python3
"""Whole-frame symbolic replay with universally quantified primary registers.

Adapted only in imports and command driver from the prior full_symbolic.py
(SHA256 c689f2dc2583e11491bd496ca902da2f13dfec781a3ed1612eb09cd224a19887). The symbolic transition and case routines are unchanged.
Original case/proof mechanism is attributed in the package NOTICE.md.

Every nonconstant primary has its own quantified natural variable. The gap
has a separate variable, and the nonempty spare suffix has an arbitrary first
value followed by an arbitrary finite block list. Register boxes are expanded.
Only checked one-block/list induction rules accelerate traversal of the tail.
"""
from pathlib import Path
from collections import Counter
import argparse, importlib.util, json, sys, time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'vendor/code'))
import rebuild_machines as rebuild
import review_affine_source as paths
from verify_reassociation import Decoder, read_json
import check_macro_inductions as m
E, Run, Blocks, Blank, Conf = m.E, m.Run, m.Blocks, m.Blank, m.Conf

def make_file(values):
    return [atom for v in values for atom in m.B(v)] + m.B(E.var('spare_first')) + [Blocks('B','spare_tail'),Blank()]

def normalize(c):
    c.left=m.norm(c.left,c.state==48 and c.side=='L')
    c.right=m.norm(c.right)

def step(c, cost, motion, trace):
    normalize(c)
    answer=m.apply_list_induction(c,cost,motion,trace)
    if answer is not None: return answer
    source=c.right if c.side=='R' else c.left
    target=c.left if c.side=='R' else c.right
    if not source: raise AssertionError('unrepresented exterior')
    if isinstance(source[0],Blank): source.insert(0,m.bit(0))
    atom=source[0]
    assert isinstance(atom,Run),(c.state,c.side,atom,'opaque list reached without a checked traversal lemma')
    w,d,q=m.TABLE[c.state,atom.bit]
    old=c.state
    if d==c.side and q==c.state:
        source.pop(0);target.insert(0,Run(w,atom.length))
        cost+=atom.length;motion+=atom.length*(1 if d=='R' else -1)
        trace.append(dict(rule='unary-induction',state=old,read=atom.bit,row=[w,d,q],repetitions=str(atom.length)))
    else:
        assert atom.length.c>=1,(old,c.side,atom,'unjustified branch')
        source[0]=Run(atom.bit,atom.length+-1)
        if d==c.side: target.insert(0,m.bit(w))
        else: source.insert(0,m.bit(w));c.side=d
        c.state=q;cost+=1;motion+=1 if d=='R' else -1
        trace.append(dict(rule='literal',state=old,read=atom.bit,row=[w,d,q]))
    normalize(c)
    return cost,motion

def case(pc,op,r,zero,intervals):
    logical=[E(lo) if lo==hi and hi<9 else E(lo)+E.var('r'+str(i)) for i,(lo,hi) in enumerate(intervals)]
    if op=='CD': logical[r]=E() if zero else E(max(1,intervals[r][0]))+E.var('r'+str(r))
    values=[None]*9
    for i,j in enumerate(rebuild.PHYSICAL): values[j]=logical[i]
    extra=0;overflow=False;output=values.copy();add_spare=False
    if op=='CI': successor,overflow=paths.full_inc(pc);output[rebuild.PHYSICAL[r]]+=1;add_spare=True
    elif op=='CD' and not zero: successor,overflow=paths.full_inc(pc);output[rebuild.PHYSICAL[r]]+=-1;extra=1
    elif op=='CD':successor,overflow=paths.full_inc(paths.full_strip(pc,'0',1))
    elif op=='CB':successor,overflow=paths.full_inc(paths.full_strip(pc,'0',r))
    elif op=='CC':successor=paths.full_strip(pc,'1',r)
    else: successor=''
    start_right=[m.bit(int(b)) for b in pc]+[Run(0,E.var('gap')+(40-len(pc))),m.bit(1)]+make_file(values)
    c=Conf(96,'R',[m.bit(1),Blank()],start_right)
    out_file=make_file(output)
    if add_spare: out_file=out_file[:-1]+m.B(E(1))+[Blank()]
    target=Conf(96,'R',[m.bit(1),Blank()],[m.bit(int(b)) for b in successor]+[Run(0,E.var('gap')+(40+extra+int(overflow)-len(successor))),m.bit(1)]+out_file)
    normalize(c);normalize(target)
    cost=E();motion=E();trace=[]
    for _ in range(3000):
        if trace and ((op=='CH' and c.state==254) or (op!='CH' and c.key()==target.key())):
            assert cost.nonnegative() and cost.c>=1,'positive progress is required'
            if op!='CH': assert motion==E(-int(overflow)),('unexpected head displacement',pc,motion)
            return dict(rules=len(trace),cost=str(cost),time_lower_bound=cost.c,motion=str(motion),trace=trace)
        cost,motion=step(c,cost,motion,trace)
    raise AssertionError(('symbolic fuel exhausted',pc,op,r,zero,c.key(),target.key()))

def main():
    assert __debug__, 'Python assertions are required.'
    table_path=ROOT/'machine/zfc_composed246_old.tm'
    m.TABLE=rebuild.read_table(table_path)[0]
    m.prove_blocks();m.prove_word_identity()
    nodes,root,_=read_json(ROOT/'sources/rotated202.json')
    source=Decoder(nodes,root)
    sites=[(pc,'C'+e[0],e[1] if len(e)==2 else None) for pc,e in source.sites]
    assert len(sites)==6460
    counts=Counter();rows=set();cases=[];began=time.monotonic()
    for i,(p,op,r) in enumerate(sites):
        for zero in ((True,False) if op=='CD' else (None,)):
            result=case(p,op,r,zero,[[0,9]]*9)
            for step in result['trace']:
                if 'state' in step:rows.add((step['state'],step['read']))
            counts['cases']+=1;counts['symbolic_rules']+=result['rules']
            cases.append(dict(index=i,pc=p,op=op,r=r,zero=zero,
                         **{k:v for k,v in result.items() if k!='trace'}))
    assert counts['cases']==8391 and len(rows)==492
    from hashlib import sha256
    result=dict(status='PASS',complete=True,
        scope='Independent primary naturals, arbitrary nonnegative extra gap and nonempty arbitrary spare suffix; no register-operation oracle.',
        table_sha256=sha256(table_path.read_bytes()).hexdigest(),
        source_sha256=sha256((ROOT/'sources/rotated202.json').read_bytes()).hexdigest(),
        checker_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        counts=dict(counts),rows=sorted(rows),cases=cases,
        minimum_steps=min(c['time_lower_bound'] for c in cases),
        seconds=time.monotonic()-began)
    (ROOT/'results/direct_whole_frame.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('rows','cases')},indent=2))

if __name__=='__main__':main()
