#!/usr/bin/env python3
"""Complete guarded affine instruction certificate for the exact cache-MP252.

Uses the unchanged, attributed strict-affine engine. Its only nonliteral
arithmetic excursions are the four published register-box contracts. Every
decrement guard is reindexed to the actual physical slot. The separate source
binding checker proves that this decoder implements the intended source edit.
"""
from collections import Counter
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys, types

ROOT=Path(__file__).resolve().parents[1]
TABLE_SHA='9ba862d15e0f689525281e1c96083acf7f389157bd56d6a2676f223106dc07a9'
PHYSICAL=(4,5,0,8,6,2,1,7,3)


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def require(value,message):
    if not value: raise ValueError(message)


def increment(path):
    bits=list(path)
    while bits and bits[-1]=='1':bits.pop()
    return ''.join(bits[:-1])+'1' if bits else None


def strip(path,bit,n):
    i=len(path)
    while n and i:
        i-=1;n-=path[i]==bit
    return path[:i]


def successor(path,op,arg,zero):
    if op=='I' or op=='D' and not zero:return increment(path)
    if op=='D':return increment(strip(path,'0',1))
    if op=='B':return increment(strip(path,'0',arg))
    if op=='C':return strip(path,'1',arg)
    return ''


def verify(output):
    require(__debug__,'Run Python with assertions enabled; do not use -O')
    table_path=ROOT/'machine/cache_mp252_old.tm'
    dag_path=ROOT/'machine/decoder_cache.json'
    engine_path=ROOT/'upstream/strict_affine.py'
    require(digest(table_path)==TABLE_SHA,'Wrong exact positive transition table')
    sys.modules['cost_search']=types.SimpleNamespace()
    spec=importlib.util.spec_from_file_location('cachemp_strict_affine',engine_path)
    engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
    table={}
    for line in table_path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();key=q,int(b)
        require(key not in table,'Duplicate row')
        table[key]=int(w),d,t
    require(len(table)==504,'Incomplete transition table')
    data=json.loads(dag_path.read_text())
    nodes={int(k):tuple(map(tuple,v)) for k,v in data['nodes'].items()}
    leaves=[];active=set()
    def walk(e,p):
        if e[0]!='N':leaves.append((p,e));return
        require(e[1] in nodes and e[1] not in active,'Invalid or cyclic source DAG')
        active.add(e[1])
        for b,child in enumerate(nodes[e[1]]):walk(child,p+str(b))
        active.remove(e[1])
    walk(('N',data['root']),'')
    require(len(leaves)==6437,'Unexpected instruction-leaf count')
    totals=Counter();cases=[]
    for path,edge in leaves:
        op=edge[0];arg=edge[1] if len(edge)>1 else None
        for zero in ((True,False) if op=='D' else (None,)):
            physical=PHYSICAL[arg] if op in ('I','D') else arg
            branch=(physical,zero) if op=='D' else None
            nxt=successor(path,op,arg,zero)
            effect=('inc',physical) if op=='I' else ('dec',physical) if op=='D' and not zero else None
            right=[('b',int(b)) for b in nxt] if nxt is not None else []
            right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
            target=engine.canon([('b',1)],right)
            rules,literal=engine.run(table,path,branch,target,halt=op=='H',fuel=1000)
            require(literal>0,'A zero-progress instruction trace was accepted')
            totals.update(rules)
            cases.append({'path':path,'operation':op,'argument':arg,'zero':zero,
                          'literal_steps':literal,'rule_counts':dict(rules)})
    require(len(cases)==8361,'Incomplete guarded case coverage')
    # Guard safety checks exercise assumptions that would otherwise hide a
    # wrong register selector. These are relevant negative controls.
    require(engine.oracle('43',None,('mark',0)) is None,'Unguarded decrement accepted')
    require(engine.oracle('43',(1,True),('mark',0)) is None,'Wrong-register decrement guard accepted')
    require(engine.oracle('64',None,('plain',('inc',0))) is None,'Second effect silently accepted')
    result={'status':'PASS','working_states':252,'instruction_leaves':len(leaves),
        'cases_checked':len(cases),'max_leaf_depth':max(len(p) for p,e in leaves),
        'minimum_literal_progress':min(x['literal_steps'] for x in cases),
        'logical_to_physical':list(PHYSICAL),'rule_counts':dict(totals),
        'input_sha256':{str(p.relative_to(ROOT)):digest(p) for p in (table_path,dag_path,engine_path)},
        'scope':'All gaps 40+n for n>=0 and all valid register files with the named decrement guard. Four unchanged unbounded register-box lemmas are used; this Python checker has not been kernel verified.',
        'negative_controls':'Unguarded decrement, wrong-register guard, and unjustified second effect all rejected',
        'cases':cases}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    return {k:v for k,v in result.items() if k!='cases'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'results/affine_verification.json')
    args=parser.parse_args();print(json.dumps(verify(args.output),indent=2))
