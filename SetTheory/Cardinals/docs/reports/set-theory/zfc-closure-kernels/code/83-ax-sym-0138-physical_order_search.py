#!/usr/bin/env python3
"""Seeded physical-dictionary search for AX row/role permutations.

The search output is a syntactic candidate only. Binary contextual contracts
and blank initialization must be checked separately.
"""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import argparse,json,random,sys,time,math,itertools
import axiom_order_search as a

HERE=Path(__file__).resolve().parent
PKG=a.ROOT/'fixtures'
D=json.loads((PKG/'closed-sequence-grammar-next22.json').read_text())
RULES={int(q):tuple(x) for q,x in D['rules'].items()}
SEM={int(q):tuple(w) for q,w in D['flattened_semantic_words'].items()}
AX=76
OP={'inc':'I','dec':'D','cont':'C','brk':'B','halt':'H'}

@lru_cache(None)
def ast(i):
    r=D['ast_dag'][i]
    return (OP[r[1][0]],*r[1][1:]) if r[0]=='L' else ('N',ast(r[1]),ast(r[2]))
@lru_cache(None)
def bd(t):
    if t[0]!='N':return (t[1] if t[0]=='B' else int(t[0]=='D'),t[1] if t[0]=='C' else 0)
    ba,ca=bd(t[1]);bb,cb=bd(t[2]);return max(ba-1,bb),max(ca,cb-1)
@lru_cache(None)
def nf(t):
    if t[0]!='N':return t
    aa,bb=nf(t[1]),nf(t[2])
    if bd(t[1])==bd(t[2])==(0,0):
        return ('S',*(aa[1:] if aa[0]=='S' else (aa,)),*(bb[1:] if bb[0]=='S' else (bb,)))
    return ('A',aa,bb)
def flat(t):
    n=nf(t);assert bd(t)==(0,0)
    return n[1:] if n[0]=='S' else (n,)
assert nf(ast(D['original_ast']))==a.normal(('N',a.DATA['root']))
ATOM_EXPAND={name:flat(ast(row['ast'])) for name,row in D['atoms'].items()}
EXPAND={q:sum((ATOM_EXPAND[s] for s in w),())for q,w in SEM.items()}
assert len(EXPAND[AX])==1270

@lru_cache(None)
def deps(q):
    if q not in RULES:return frozenset()
    x,y=RULES[q];return frozenset((q,))|deps(x)|deps(y)
BASE=frozenset().union(*(deps(q)for q in D['required_entry_roots']if q!=AX))
assert AX not in BASE
OLD_BY_WORD={w:q for q,w in SEM.items()}
PERMS=list(itertools.permutations('abc'))
def renamed(form,p):
    if isinstance(form,str):return dict(zip('abc',p)).get(form,form)
    if isinstance(form,tuple):return form[0],renamed(form[1],p),renamed(form[2],p)
    return form
PREFIX=sum((a.MACROS[m]for m in [166,121,180,176]),())
ROW_WORDS=[[sum((a.MACROS[m]for m in a.theory.emit(renamed(row,p))),())for p in PERMS]for row in a.ROWS[1:]]
ORIG_PREFIX=PREFIX+sum((variants[0]for variants in ROW_WORDS),())
assert EXPAND[AX][:len(ORIG_PREFIX)]==ORIG_PREFIX
SUFFIX=EXPAND[AX][len(ORIG_PREFIX):]

PATTERNS=defaultdict(list)
for q,w in EXPAND.items():
    if q==AX:continue
    PATTERNS[w[0]].append((w,SEM[q],q))
for sym,w in ATOM_EXPAND.items():PATTERNS[w[0]].append((w,(sym,),None))
for k in PATTERNS:PATTERNS[k].sort(key=lambda z:-len(z[0]))

def parse(target,rng,style=0):
    cost=[float('inf')]*(len(target)+1);choices=[None]*len(target);cost[-1]=0
    weights={q:(0 if q in BASE else (.08+.1*rng.random()if style==0 else .25+.5*rng.random()))for q in RULES}
    for i in range(len(target)-1,-1,-1):
        for pattern,sem,q in PATTERNS[target[i]]:
            j=i+len(pattern)
            if target[i:j]!=pattern:continue
            local=1+sum(weights[d]for d in deps(q)) if q is not None else 1
            val=cost[j]+local
            if val<cost[i]:cost[i]=val;choices[i]=(j,sem,q)
    assert choices[0]is not None
    tokens=[];pos=0
    while pos<len(target):
        j,sem,q=choices[pos];tokens.append(sem);pos=j
    return tokens

def build(tokens,rng):
    # Old phrase definitions are retained exactly; all newly introduced
    # concatenations can reuse a complete old semantic word.
    rules={SEM[q]:(SEM[x]if x in SEM else (D['flattened_semantic_words'][str(q)][0],),
                       SEM[y]if y in SEM else (D['flattened_semantic_words'][str(q)][-1],))for q,(x,y)in RULES.items()}
    # Construct old splits by their known flattened lengths, which distinguishes
    # variants of the same physical atom in the two incoming contexts.
    for q,(x,y)in RULES.items():
        left=SEM[x] if x in SEM else SEM[q][:1]
        right=SEM[y] if y in SEM else SEM[q][-1:]
        assert left+right==SEM[q]
        rules[SEM[q]]=left,right
    root=sum(tokens,())
    def group(parts):
        if len(parts)==1:return parts[0]
        whole=sum(parts,())
        if whole in rules:return whole
        options=[]
        for cut in range(1,len(parts)):
            left=sum(parts[:cut],());right=sum(parts[cut:],())
            score=int(len(left)==1 or left in rules)+int(len(right)==1 or right in rules)
            options.append((score+rng.random()*.1,cut))
        cut=max(options)[1];left=group(parts[:cut]);right=group(parts[cut:]);rules[whole]=left,right;return whole
    group(tokens)
    roots=[root if q==AX else SEM[q] for q in D['required_entry_roots']]
    live=set();todo=list(roots)
    while todo:
        w=todo.pop()
        if len(w)==1 or w in live:continue
        live.add(w);todo.extend(rules[w])
    return {w:rules[w]for w in live},roots

def search(runs,seed,out):
    rng=random.Random(seed);out.mkdir(parents=True,exist_ok=True);beg=time.monotonic();best=999;history=[]
    elite=(tuple(range(8)),(0,)*8)
    for trial in range(runs):
        if trial==0:order,roles=elite
        else:
            order,roles=map(list,elite)
            if rng.random()<.3:
                i,j=rng.sample(range(8),2);order[i],order[j]=order[j],order[i]
            else:roles[rng.randrange(8)]=rng.randrange(6)
            if trial%15==14:order=rng.sample(range(8),8);roles=[rng.randrange(6)for _ in range(8)]
            order,roles=tuple(order),tuple(roles)
        target=PREFIX+sum((ROW_WORDS[i][roles[i]]for i in order),())+SUFFIX
        if trial==0:
            tokens=[SEM[AX]]
        else:tokens=parse(target,rng,trial%3==2)
        rules,roots=build(tokens,rng);score=len(rules)
        assert sum((ATOM_EXPAND[s]for s in roots[D['required_entry_roots'].index(AX)]),())==target
        if score<best:
            best=score;elite=order,roles
            rec=dict(trial=trial,rules=score,naive_states=119+score,order=order,roles=roles,seconds=time.monotonic()-beg)
            history.append(rec)
            data=dict(**rec,grammar=[dict(word=w,left=p[0],right=p[1])for w,p in rules.items()],roots=roots,
                      scope='Syntactic physical grammar only; no contextual or blank-start validation')
            (out/f'candidate_{trial}_{score}.json').write_text(json.dumps(data,indent=2)+'\n')
            (out/'best.json').write_text(json.dumps(data,indent=2)+'\n')
            print('BEST',rec,flush=True)
        if score==best and rng.random()<.3:elite=order,roles
        if trial%100==0:print('progress',trial,'best',best,'seconds',time.monotonic()-beg,flush=True)
    result=dict(runs=runs,best_rules=best,seconds=time.monotonic()-beg,history=history)
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=3000);ap.add_argument('--seed',type=int,default=7310246);ap.add_argument('--output',type=Path,default=a.ROOT/'results/rerun_physical_order');args=ap.parse_args()
    print('fixed nonAX phrases',len(BASE),'original AX-exclusive',len(RULES)-len(BASE),'patterns',sum(map(len,PATTERNS.values())),flush=True)
    search(args.runs,args.seed,args.output)
