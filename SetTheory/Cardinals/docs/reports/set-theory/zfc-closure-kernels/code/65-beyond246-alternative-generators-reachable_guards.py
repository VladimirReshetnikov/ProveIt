#!/usr/bin/env python3
"""Generate a small-value product invariant for the native program.

The graph is extracted from the full prefix tree, with zero counter padding.
The default domain distinguishes zero, one, and values at least two. The
refinement script reuses this worklist with a larger exact-value domain.
"""
from pathlib import Path
from collections import deque,Counter
import argparse,hashlib,json,re,sys
HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
PROGRAM_SHA256='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def program_sites():
    """Parser ported from the inherited context246 rebuild_machines.py.

    The generator uses its original counter normalization below. The separate
    verify_invariant.py reparses the tree and retains cleared carry zeros.
    """
    raw=(PACKAGE/'reference/Prog254.v').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==PROGRAM_SHA256
    source=raw.decode('ascii').split('Definition p254_tab',1)[1]
    body=source.split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    pattern=r'\(('+edge+r'),\s*('+edge+r')\)'
    rows=re.findall(pattern,body)
    assert len(rows)==6459
    assert not re.sub(r'[\s;]','',re.sub(pattern,'',body))
    seen,sites=set(),[]
    def visit(node,prefix,active):
        assert node not in active and 0<=node<len(rows)
        seen.add(node)
        for bit,term in enumerate(rows[node]):
            kind,*arg=term.split()
            value=int(arg[0]) if arg else None
            pc=prefix+str(bit)
            if kind=='CN':visit(value,pc,active|{node})
            else:
                if kind in ('CI','CD'):assert value in range(9)
                sites.append((pc,kind,value))
    visit(0,'',set())
    assert seen==set(range(6459)) and len(sites)==6460
    assert len({pc for pc,kind,value in sites})==6460
    return sites

SITES=program_sites()
BYPC={pc:i for i,(pc,op,r) in enumerate(SITES)}
PREFIXES={pc[:j] for pc,op,r in SITES for j in range(len(pc)+1)}

def decode(pc):
    word=pc+'0'*40
    for i in range(len(word)+1):
        if word[:i] in BYPC:
            assert all(x=='0' for x in word[i:]),('nonzero suffix at leaf',pc,word[:i])
            return BYPC[word[:i]]
    raise AssertionError(pc)

def increment(pc):
    return '' if '0' not in pc else pc[:pc.rindex('0')]+'1'

def strip(pc,symbol,count):
    while pc and count:
        count-=pc[-1]==symbol
        pc=pc[:-1]
    return pc

def successor(pc,op,r,zero):
    if op=='CI' or op=='CD' and not zero:p=increment(pc)
    elif op=='CD':p=increment(strip(pc,'0',1))
    elif op=='CB':p=increment(strip(pc,'0',r))
    elif op=='CC':p=strip(pc,'1',r)
    else:return None
    return decode(p)

EDGES={}
for i,(pc,op,r) in enumerate(SITES):
    for zero in ((True,False) if op=='CD' else (None,)):
        EDGES[i,zero]=successor(pc,op,r,zero)

def advance(v,op,r,zero):
    if op=='CD' and not(v[r]&(1 if zero else 6)):return None
    out=list(v)
    if op=='CI':out[r]=(2 if v[r]&1 else 0)|(4 if v[r]&6 else 0)
    if op=='CD':out[r]=1 if zero else ((1 if v[r]&2 else 0)|(6 if v[r]&4 else 0))
    return tuple(out)

def run(start):
    root=decode('');a=[None]*len(SITES);a[root]=start
    todo=deque([root]);queued={root};steps=0
    while todo:
        i=todo.popleft();queued.remove(i);pc,op,r=SITES[i];steps+=1
        for zero in ((True,False) if op=='CD' else (None,)):
            v=advance(a[i],op,r,zero);j=EDGES[i,zero]
            if v is None or j is None:continue
            joined=v if a[j] is None else tuple(x|y for x,y in zip(a[j],v))
            if joined!=a[j]:
                a[j]=joined
                if j not in queued:todo.append(j);queued.add(j)
    # Independently check the candidate inductive invariant without a worklist.
    assert all((u & v)==u for u,v in zip(start,a[root]))
    allowed=[];rejected=[]
    for i,(pc,op,r) in enumerate(SITES):
        for zero in ((True,False) if op=='CD' else (None,)):
            v=None if a[i] is None else advance(a[i],op,r,zero)
            if v is None:rejected.append([pc,op,r,zero]);continue
            allowed.append([pc,op,r,zero]);j=EDGES[i,zero]
            if j is not None:
                assert a[j] is not None
                assert all((x&y)==x for x,y in zip(v,a[j]))
    return dict(root=root,initial=list(start),invariants=a,allowed=allowed,rejected=rejected,iterations=steps,
        reachable_sites=sum(x is not None for x in a),allowed_cases=len(allowed),rejected_cases=len(rejected),
        rejected_kinds=dict(Counter(x[1] for x in rejected)))

def graph_summary():
    return dict(status='PASS',program_sha256=PROGRAM_SHA256,source_nodes=6459,
        instruction_sites=len(SITES),guarded_cases=len(EDGES),root_site=decode(''),
        path_length_range=[min(len(x[0]) for x in SITES),max(len(x[0]) for x in SITES)],
        operation_counts=dict(Counter(x[1] for x in SITES)))

def arguments(description):
    parser=argparse.ArgumentParser(description=description)
    parser.add_argument('--output-dir',type=Path,
        help='Required for generation. Existing output files are never overwritten.')
    parser.add_argument('--parse-only',action='store_true',
        help='Parse the pinned source and construct all guarded CFG edges, then exit.')
    return parser

def prepare_output(args,parser,names):
    if not __debug__:parser.error('Assertions required; do not use -O or -OO.')
    if args.parse_only:
        print(json.dumps(graph_summary(),indent=2));return None
    if args.output_dir is None:parser.error('--output-dir is required unless --parse-only is used.')
    output=args.output_dir.resolve()
    output.mkdir(parents=True,exist_ok=True)
    existing=[name for name in names if (output/name).exists()]
    if existing:parser.error('Refusing to overwrite: '+', '.join(existing))
    return output

def write_json(path,value):
    with path.open('x',encoding='utf-8') as f:
        f.write(json.dumps(value,indent=2)+'\n')

def main():
    parser=arguments(__doc__);args=parser.parse_args()
    output=prepare_output(args,parser,['reachable-guards.json','product-invariant.json'])
    if output is None:return
    # Every six-nonformula safe root: N,A,D,X,Y,L arbitrary; T=W=H zero.
    initial=(7,1,1,7,7,1,7,7,7)
    generic=run(initial)
    # A smaller abstract root family containing the actual N=D=3 root.
    actual_root_abstraction=run((4,1,1,1,4,1,1,1,1))
    write_json(output/'reachable-guards.json',dict(status='PASS',generic=generic,
        actual_root_abstraction=actual_root_abstraction))
    excluded=[];index=0
    for i,(pc,op,k) in enumerate(SITES):
        for zero in ((True,False) if op=='CD' else (None,)):
            if [pc,op,k,zero] in generic['rejected']:excluded.append(index)
            index+=1
    certificate=dict(format='native-prefix-tree-product-invariant-v1',
        program_sha256=PROGRAM_SHA256,categories=['0','1','at least2'],
        logical_register_order=['N','T','W','A','D','H','X','Y','L'],
        initial_masks=list(initial),excluded_case_indices=excluded,masks=generic['invariants'])
    write_json(output/'product-invariant.json',certificate)
    for name,value in [('generic',generic),('actual_root_abstraction',actual_root_abstraction)]:
        print(name,{k:v for k,v in value.items() if k not in ('invariants','allowed','rejected')})

if __name__=='__main__':main()
