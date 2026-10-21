#!/usr/bin/env python3
"""Ten four-leaf binary prefix codecs with I(0,0)=0 and R(0,0)=1.

Exhaustively enumerate the five four-leaf prefix-tree shapes and the two
assignments of the remaining leaves to Q/E.  Explore compact CI1-only trees
for changed scale factors and offsets.  Results are compiler costs, not
candidate runtime certificates.  The MP comparison builder is included.
"""
import itertools,json,time,collections
from functools import cache
from pathlib import Path
import encoding_support as x
s,b,z,W=x.s,x.b,x.z,x.W
base=W/'K220_Construction_2026-10-20/machine'
T=b.read_table((base/'k220.native.tm').read_bytes())
S=json.loads((base/'sites220.json').read_text());old=s.tree(S)
word=tuple(tuple(r[1:])for r in S);imp=z.MACRO[119];iw=x.flat(imp);inc=('CI',1)
occ=[]
for i in range(len(word)-len(iw)+1):
    if word[i:i+len(iw)]!=iw:continue
    j=i+len(iw);k=0
    while j+k<len(word)and word[j+k]==inc:k+=1
    occ.append((i,j,k))
assert collections.Counter(k for i,j,k in occ)=={0:41,1:12,2:22,3:6}
assert occ[-1]==(4678,4705,0)
builder={(i,j):k for i,j,k in occ};tagleaf={j+h:(k,h)for i,j,k in occ for h in range(k)}


@cache
def trees(n):
    if n==1:return (inc,)
    return tuple((a,b)for k in range(1,n)for a in trees(k)for b in trees(n-k))


@cache
def nodes(n):
    return frozenset((n,))if s.leaf(n)else nodes(n[0])|nodes(n[1])|{n}


@cache
def info(n):
    if s.leaf(n):return (1,0,0,0)
    a,bb=info(n[0]),info(n[1]);lead=1+a[1]
    return a[0]+bb[0],lead,max(lead,a[2],bb[2]),1+max(a[3],bb[3])


oldnodes=nodes(old)
def choices(n):
    if n==0:return (None,)
    alltrees=trees(n)
    best=min(len(nodes(t)-oldnodes)for t in alltrees)
    # Keep all trees within one new DAG node of the best CI-only grammar.
    return tuple(t for t in alltrees if len(nodes(t)-oldnodes)<=best+1)


pair=(inc,inc);quad=(pair,pair)
assert imp[-1][-1]==(('CD',7),(quad,('CC',2)))
def scaler(body):return(imp[0],(imp[1][0],(('CD',7),(body,('CC',2)))))


def skeleton(n,start=0):
    stop=start+len(x.flat(n))
    if(start,stop)in builder:return('B',builder[start,stop])
    if s.leaf(n):return('T',*tagleaf[start])if start in tagleaf else('F',n)
    return('N',skeleton(n[0],start),skeleton(n[1],start+len(x.flat(n[0]))))
SK=skeleton(old)


def source(codec,body8,qchoice,echoice):
    scaled={2:scaler(pair),4:imp,8:scaler(body8)}
    bs=[scaled[m]for m,t in codec]
    qs,es=qchoice,echoice
    @cache
    def go(sk):
        kind=sk[0]
        if kind=='F':return sk[1]
        if kind=='B':return bs[sk[1]]
        if kind=='T':
            k,h=sk[1:]
            if k==1:return inc
            pos,repl=(qs if k==2 else es)
            return repl if h==pos else inc
        l,r=go(sk[1]),go(sk[2])
        return r if l is None else l if r is None else(l,r)
    return go(SK)


def tag_choices(oldtag,newtag):
    if oldtag==newtag:return((0,inc),)
    if newtag==oldtag-1:return tuple((k,None)for k in range(oldtag))
    return tuple((k,t)for k in range(oldtag)for t in choices(newtag-oldtag+1))


def codecs():
    answer=[]
    # trees(4) uses only binary structure; leaf labels are immaterial here.
    for tr in trees(4):
        leaves=[]
        def go(t,coef=1,offset=0):
            if s.leaf(t):leaves.append((coef,offset));return
            go(t[0],2*coef,offset);go(t[1],2*coef,offset+coef)
        go(tr)
        ii=[t for t in leaves if t[1]==0];rr=[t for t in leaves if t[1]==1]
        assert len(ii)==len(rr)==1
        others=[t for t in leaves if t not in (ii[0],rr[0])]
        for q,e in (others,others[::-1]):answer.append((ii[0],rr[0],q,e))
    assert len(set(answer))==10
    return answer


out=W/'prefix_codecs';out.mkdir(exist_ok=True)
summary=[];start=time.time()
for ci,codec in enumerate(codecs()):
    # The balanced current codec and Q/E swap are already measured elsewhere;
    # keep them as control layouts without expanding their global run grammar.
    b8s=choices(8)if any(m==8 for m,t in codec)else((quad,quad),)
    qs=tag_choices(2,codec[2][1]);es=tag_choices(3,codec[3][1])
    hist=collections.Counter();best_any=999;best_allowed=999;best=[];seen=set();count=0
    for bi,b8 in enumerate(b8s):
        for qi,q in enumerate(qs):
            for ei,e in enumerate(es):
                new=source(codec,b8,q,e)
                if new in seen:continue
                seen.add(new);count+=1
                n=len(nodes(new));stats=info(new);hist[n]+=1;best_any=min(best_any,n)
                if stats[2]>6:continue
                if n<best_allowed:best_allowed=n;best=[]
                if n==best_allowed and len(best)<12:best.append((new,bi,qi,ei,stats))
    print('CODEC',ci,codec,'layouts',count,'DAG',best_any,'DAGzero6',best_allowed,'seconds',round(time.time()-start,1),flush=True)
    rows=[]
    for k,(new,bi,qi,ei,stats)in enumerate(best):
        rec={'codec_I_R_Q_E':codec,'body8_choice':bi,'q_choice':qi,'e_choice':ei,
             'metrics':{'dag_nodes':len(nodes(new)),'leaf_occurrences':stats[0],
                        'maximum_zero_run':stats[2],'maximum_depth':stats[3]},
             'status':'COMPILER_COST_ONLY; EXACT_SOURCE_AND_RUNTIME_CALIBRATION_REQUIRED',
             'MP_builder_included':[4678,4705]}
        dd=out/f'codec{ci}_best{k}';dd.mkdir(exist_ok=True)
        rr=s.sites(new);assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)
        (dd/'sites.json').write_bytes(s.compact(rr))
        try:
            U,c=z.compile_tree(T,old,new);rec['compiler']=c
            (dd/'candidate.tm').write_bytes(b.table_bytes(U))
        except Exception as exc:rec['error']=repr(exc)
        (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');rows.append(rec)
    item={'codec_I_R_Q_E':codec,'layouts':count,'histogram_DAG':dict(hist),
          'minimum_DAG':best_any,'minimum_DAG_zero6':best_allowed,'best_layouts':rows}
    summary.append(item)
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('DONE',round(time.time()-start,1),'seconds',flush=True)
