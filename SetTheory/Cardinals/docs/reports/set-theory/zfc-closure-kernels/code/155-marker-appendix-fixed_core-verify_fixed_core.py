#!/usr/bin/env python3
"""Reconstruct and inspect the fixed-core source evidence, without a compiler.

The finite structural checks do not claim a binary machine, an initialized
runtime, a new block compiler, or a proof-assistant theorem. The all-natural
formula-emission argument uses the explicitly stated inherited macro contracts.
"""
from pathlib import Path
from functools import lru_cache
import argparse,hashlib,json,sys
if not __debug__ or sys.flags.optimize:
    raise SystemExit('Refusing optimized Python: this verifier requires assertions; run without -O/-OO/PYTHONOPTIMIZE.')
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('package',nargs='?',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--output',type=Path)
args=ap.parse_args();P=args.package
sha=lambda raw:hashlib.sha256(raw).hexdigest()
manifest=json.loads((P/'provenance.json').read_text())
for r in manifest['files']:
    assert sha((P/r['artifact']).read_bytes())==r['sha256'],('input identity',r['artifact'])
def leaf(t):return isinstance(t[0],str)
def frozen(t):return tuple(frozen(x)for x in t)if isinstance(t,list)else t
@lru_cache(None)
def flat(t):return(t,)if leaf(t)else flat(t[0])+flat(t[1])
@lru_cache(None)
def size(t):return 1 if leaf(t)else size(t[0])+size(t[1])
@lru_cache(None)
def boundary(t):
    if leaf(t):
        op,r=t
        return(1,0,False)if op=='CD'else(r,0,False)if op=='CB'else(0,r,False)if op=='CC'else(0,0,op=='CH')
    a,b=map(boundary,t)
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0),a[2]or b[2]
def sites(t,p=''):
    return[[p,*t]]if leaf(t)else sites(t[0],p+'0')+sites(t[1],p+'1')
def parse(raw):
    rr=json.loads(raw);dd={p:(op,r)for p,op,r in rr};assert len(dd)==len(rr)
    def go(p=''):
        if p in dd:return dd[p]
        assert any(q.startswith(p)for q in dd),('missing subtree',p)
        return go(p+'0'),go(p+'1')
    tree=go();assert sites(tree)==rr;return tree

def metrics(t):
    live=set()
    def go(v):
        if v in live:return
        live.add(v)
        if not leaf(v):go(v[0]);go(v[1])
    go(t);rr=sites(t)
    return dict(dag_nodes=len(live),leaf_occurrences=len(rr),maximum_depth=max(len(p)for p,op,r in rr),maximum_zero_run=max(len(x)for p,op,r in rr for x in p.split('1')))
def serial(xs):return xs[0]if len(xs)==1 else(xs[0],serial(xs[1:]))
def forest(t,lo,hi):
    out=[]
    def go(v,i=0):
        j=i+size(v)
        if j<=lo or hi<=i:return
        if lo<=i and j<=hi:
            assert boundary(v)==(0,0,False),('open factor',i,j)
            out.append(v);return
        assert not leaf(v);go(v[0],i);go(v[1],i+size(v[0]))
    go(t);assert sum(map(size,out))==hi-lo;return serial(out)
def splice(t,lo,hi,replacement):
    inserted=[]
    def go(v,i=0):
        j=i+size(v)
        if j<=lo or hi<=i:return v
        if lo<=i and j<=hi:
            assert boundary(v)==(0,0,False)
            if i==lo:inserted.append(i);return replacement
            return None
        assert not leaf(v);a=go(v[0],i);b=go(v[1],i+size(v[0]))
        if a is None and b is not None:assert boundary(b)==(0,0,False);return b
        if b is None and a is not None:assert boundary(a)==(0,0,False);return a
        return None if a is None else(a,b)
    ans=go(t);assert inserted==[lo];return ans

def cfg(t):
    n=size(t);out=[]
    def go(v,i,breaks,continues):
        if leaf(v):
            op,r=v;assert len(out)==i;next_i=(i+1)%n
            if op=='CI':ds=(next_i,)
            elif op=='CD':ds=(breaks[0]if breaks else 0,next_i)
            elif op=='CB':ds=(breaks[r-1]if r<=len(breaks)else 0,)
            elif op=='CC':ds=(continues[r-1]if r<=len(continues)else 0,)
            else:assert op=='CH';ds=()
            out.append((op,r if op in('CI','CD')else None,ds));return
        a,b=v;mid=i+size(a);end=(mid+size(b))%n
        go(a,i,[end]+breaks,continues);go(b,mid,breaks,[i]+continues)
    go(t,0,[],[]);return out

def path_cfg(rr):
    ranges={};n=len(rr)
    for i,(p,op,r)in enumerate(rr):
        for j in range(len(p)+1):
            pref=p[:j]
            if pref not in ranges:ranges[pref]=[i,i+1]
            else:ranges[pref][1]=i+1
    def target(p,bit,k):
        for j in range(len(p)-1,-1,-1):
            if p[j]==bit:
                k-=1
                if k==0:return ranges[p[:j]][1 if bit=='0'else 0]%n
        return 0
    return[(op,r if op in('CI','CD')else None,(i+1 if i+1<n else 0,)if op=='CI'else(target(p,'0',1),(i+1)%n)if op=='CD'else(target(p,'0',r),)if op=='CB'else(target(p,'1',r),)if op=='CC'else())for i,(p,op,r)in enumerate(rr)]

baseline=parse((P/'source/baseline_dominated203.json').read_text())
mac={k:frozen(v)for k,v in json.loads((P/'source/macros.json').read_text()).items()}
a,b,c,imp=[mac[k]for k in('a','b','c','I')];push=a[0];inc=('CI',1)
for k,(lo,hi)in{'a':(40,66),'b':(66,92),'c':(121,147),'I':(92,119)}.items():
    assert flat(mac[k])==flat(baseline)[lo:hi]
assert all(boundary(v)==(0,0,False)for v in mac.values())
old_v=forest(baseline,2657,2899);old_j=forest(baseline,2899,4496);neg_tail=forest(baseline,4523,4570)
assert flat(neg_tail)==flat((push,inc))+flat(imp)
F=(push,inc)
def construct(labels):
    aa,bb,offset=labels
    newa=F if aa==1 else push
    newb=(F,(inc,inc))if bb==3 else F
    extra=((inc,inc),(inc,inc))if offset==4 else(inc,inc)
    newc=(c,extra)
    def rep(t):
        if t==a:return newa
        if t==b:return newb
        if t==c:return newc
        return t if leaf(t)else(rep(t[0]),rep(t[1]))
    insert=((rep(old_j),neg_tail),old_v)
    assert boundary(insert)==(0,0,False)
    return splice(baseline,2657,4570,insert),insert,newa,newb,newc

I=lambda x,y:('I',x,y)
Q=lambda x,y:('Q',x,y)
R=lambda x,y:('R',x,y)
N=lambda x:I(x,1)
def req(b,k,m):return Q(b,I(m,N(Q(b,I(m,N(R(b,k)))))))
def clos(a,b,k,m):return Q(b,I(R(b,k),N(Q(a,I(m,N(Q(a,I(Q(k,I(R(k,a),R(k,b))),req(b,k,m)))))))))
def nks(a,b,c):return Q(c,I(clos(a,b,c,c),N(req(b,c,c))))
def formulas(insert,newa,newb,newc,labels):
    aa,bb,offset=labels
    atoms={'a':(a,'a'),'b':(b,'b'),'c':(c,'c'),'F':(F,1),'fixed_a':(newa,aa),'fixed_b':(newb,bb),'fixed_c':(newc,('add','c',offset))}
    words=[(flat(v),('atom',value),name)for name,(v,value)in atoms.items()]
    words.extend((flat(v),('op',name),name)for name,v in [('I',imp),('R',(imp,inc)),('Q',(imp,(inc,inc)))])
    # Equal primitive words must denote equal natural values.
    meanings={}
    for word,meaning,name in words:
        assert word not in meanings or meanings[word]==meaning,('ambiguous macro',name)
        meanings[word]=meaning
    seq=flat(insert);pos=0;stack=[];tokens=[]
    while pos<len(seq):
        options=[(len(word),meaning)for word,meaning in meanings.items()if seq[pos:pos+len(word)]==word]
        assert options,('unmatched postfix macro',pos)
        length,meaning=max(options,key=lambda p:p[0]);pos+=length;tokens.append(meaning)
        if meaning[0]=='atom':stack.append(meaning[1])
        else:
            right,left=stack.pop(),stack.pop();stack.append({'I':I,'R':R,'Q':Q}[meaning[1]](left,right))
    want=[N(nks(aa,bb,('add','c',offset))),I(R('a','b'),Q('c',R('a','b')))]
    assert stack==want,('formula word',stack,want)
    return tokens

reports=[]
for labels,name in[((1,3,4),'fixed13_direct211.json'),((0,1,2),'fixed01_direct210.json')]:
    tree,insert,na,nb,nc=construct(labels);raw=(json.dumps(sites(tree),separators=(',',':'))+'\n').encode()
    assert raw==(P/'source'/name).read_bytes(),('exact reconstruction',name)
    rr=sites(tree);assert cfg(tree)==path_cfg(rr)
    original_outside={p:(op,r)for p,op,r in sites(baseline)if not p.startswith('11101001001')}
    assert original_outside=={p:(op,r)for p,op,r in rr if not p.startswith('11101001001')}
    tokens=formulas(insert,na,nb,nc,labels)
    reports.append(dict(file=name,sha256=sha(raw),labels=labels[:2],private_code='c+'+str(labels[2]),metrics=metrics(tree),macro_tokens=len(tokens),emitted_formulas=['N(nks(%s,%s,c+%s))'%labels,'gated V(a,b,c)'],outside_AX_primitives_preserved=len(original_outside),gate='Original two equality gates now guard V; the fixed core is built before V with its own code>=offset.',calibration='ordinary fixed-core theorem applies directly'if labels==(1,3,4)else'requires a separate variable-renaming adaptation of the lower proof; not a premise of the proved fixed1,3 theorem'))
opt=parse((P/'source/fixed01_reassociated210.json').read_text());direct=construct((0,1,2))[0]
assert flat(opt)==flat(direct)and cfg(opt)==cfg(direct)==path_cfg(sites(opt))
reports.append(dict(file='fixed01_reassociated210.json',sha256=sha((P/'source/fixed01_reassociated210.json').read_bytes()),metrics=metrics(opt),validation='exact primitive word and full guarded CFG equal the direct0,1 source',calibration='same separate variable-renaming obligation as direct0,1; not used by K217 or fixed1,3 theorem'))
out=dict(status='EXACT_FIXED_CORE_SOURCE_RECONSTRUCTION_PASS',source_only=True,baseline_metrics=metrics(baseline),construction_interval=[2657,4570],macro_contracts='Inherited closed parameter loads push old top, preserve parameters, and clear scratch; I/R/Q construct literal numerical operations. Constants use push-zero plus increments of top only.',reports=reports,scope='Finite exact construction, all-natural symbolic emitted formula equality under inherited macro contracts, closed splice checks, exact CFG checks, and metrics. No binary compilation, startup, universal binary runtime, or complete altered command-block compiler is claimed. The 1,3 calculus theorem is proved in the accompanying ordinary mathematical text; the 0,1 theorem adaptation is not supplied.')
if args.output:args.output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
