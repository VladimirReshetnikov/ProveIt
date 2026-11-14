#!/usr/bin/env python3
"""Experimental straight-line grammar search for the unchanged PA196 AX word."""
from pathlib import Path
import re, json, random, collections, sys, math, time

ROOT=Path(__file__).resolve().parent.parent/'bb196'
OUT=Path(__file__).resolve().parent

def parse_program(path=ROOT/'PA196/Program.lean'):
    nodes={}
    for line in path.read_text().splitlines():
        m=re.fullmatch(r'def (\w+) : Tree := (.+)',line)
        if not m: continue
        name,expr=m.groups()
        toks=re.findall(r'\.\w+|\w+|[()]',expr)
        def parse(i):
            t=toks[i]
            if t=='(':
                a,j=parse(i+1); assert toks[j]==')'; return a,j+1
            if t=='.node':
                a,j=parse(i+1); b,j=parse(j); return (a,b),j
            if t=='.leaf':
                assert toks[i+1]=='('
                op=toks[i+2][1:]
                if toks[i+3]==')': return (op,),i+4
                return (op,int(toks[i+3])),i+5
            return nodes[t],i+1
        val,j=parse(0); assert j==len(toks), (name,toks[j:]); nodes[name]=val
    return nodes

def isleaf(t): return isinstance(t[0],str)
def flatten(t,p=()):
    if isleaf(t): return [(p,t)]
    return flatten(t[0],p+(0,))+flatten(t[1],p+(1,))

def resolve(t):
    flat=flatten(t)
    def lookup(p):
        cur=t; off=0
        for bit in p:
            if isleaf(cur):
                if any(p[len_path:]): return None
                return off
            if bit: off+=size(cur[0])
            cur=cur[bit]
        return off
    def locate(p):
        if p is None: return None
        for i,(q,_) in enumerate(flat):
            if q[:len(p)]==p or p[:len(q)]==q and not any(p[len(q):]): return i
        raise ValueError(('unresolved',p))
    def succ(p):
        p=list(p)
        while p and p[-1]: p.pop()
        if not p:return None
        p[-1]=1;return tuple(p)
    def cut(p,b,k):
        p=list(p)
        while k:
            if not p:raise ValueError(('bad cut',b,k))
            if p.pop()==b:k-=1
        return tuple(p)
    code=[]
    for i,(p,op) in enumerate(flat):
        if op[0]=='inc': code.append(('inc',op[1],locate(succ(p))))
        elif op[0]=='dec': code.append(('dec',op[1],locate(succ(cut(p,0,1))),locate(succ(p))))
        elif op[0]=='breakTo':code.append(('jump',locate(succ(cut(p,0,op[1])))))
        elif op[0]=='continueTo':code.append(('jump',locate(cut(p,1,op[1]))))
        else: code.append(('halt',))
    return code

def size(t):return 1 if isleaf(t) else size(t[0])+size(t[1])

def get_macro_tree():
    ns=parse_program()
    macro={ns['node49']:'P',ns['node55']:'D',ns['node58']:'H',ns['node70']:'A',
           ns['node65']:'C',('inc',1):'i',ns['node72']:'J',ns['node75']:'K',
           ns['node142']:'L',ns['node150']:'G',('breakTo',1):'X'}
    def cvt(t):
        if t in macro:return macro[t]
        assert not isleaf(t),t
        return cvt(t[0]),cvt(t[1])
    return ns,macro,cvt(ns['x67'])

def word(t): return t if isinstance(t,str) else word(t[0])+word(t[1])
def nodes(t):return set() if isinstance(t,str) else {t}|nodes(t[0])|nodes(t[1])
def count(t):return len(nodes(t))
def replace(t,a,b):
    if t==a:return b
    return t if isinstance(t,str) else (replace(t[0],a,b),replace(t[1],a,b))

def greedy(t):
    # Rotations applied to every occurrence of a DAG node.
    while True:
        before=count(t); opts=[]
        for q in nodes(t):
            l,r=q
            if isinstance(l,tuple):opts.append((q,(l[0],(l[1],r))))
            if isinstance(r,tuple):opts.append((q,((l,r[0]),r[1])))
        best=t; score=before
        for a,b in opts:
            new=replace(t,a,b); s=count(new)
            if s<score:best,score=new,s
        if score==before:return t
        t=best

def optimal_reparse(t):
    # Cost zero for existing grammar symbols; simple length-optimal parse yields
    # alternative larger nodes without new pieces.
    W=word(t); ns=nodes(t)
    pieces={word(n):n for n in ns}
    for c in set(W): pieces[c]=c
    new=t
    for bad in sorted(ns,key=lambda x:len(word(x))):
        s=word(bad); choices={k:v for k,v in pieces.items() if k!=s}
        dp=[None]*(len(s)+1);dp[0]=(0,[])
        for i in range(len(s)):
            if dp[i] is None:continue
            for p,v in choices.items():
                if s.startswith(p,i):
                    sc=dp[i][0]+1; j=i+len(p)
                    if dp[j] is None or sc<dp[j][0]:dp[j]=(sc,dp[i][1]+[v])
        if dp[-1][0]==2:
            alt=tuple(dp[-1][1]); trial=replace(new,bad,alt)
            if count(trial)<count(new):new=trial
    return greedy(new)

def main():
    ns,macro,base=get_macro_tree()
    print('macro word',word(base),'length',len(word(base)),'nodes',count(base),flush=True)
    best=greedy(base);print('greedy',count(best),flush=True)
    best=optimal_reparse(best);print('reparse',count(best),flush=True)
    (OUT/'macro_baseline.json').write_text(json.dumps(base))
    (OUT/'macro_best.json').write_text(json.dumps(best))
    if '--search' not in sys.argv:return
    rng=random.Random(1043)
    start=time.time(); incumbent=best; score=count(best)
    for restart in range(1000):
        cur=incumbent if restart%3 else base; cs=count(cur)
        for k in range(2500):
            q=rng.choice(list(nodes(cur))); l,r=q
            if isinstance(l,tuple) and (isinstance(r,str) or rng.random()<.5): alt=(l[0],(l[1],r))
            elif isinstance(r,tuple):alt=((l,r[0]),r[1])
            else: continue
            new=replace(cur,q,alt); newscore=count(new)
            temp=0.1+1.0*(1-(k/2500))**3
            if newscore<=cs or rng.random()<math.exp((cs-newscore)/temp):cur,cs=new,newscore
            if cs<score:
                incumbent,score=cur,cs
                print('BEST',score,'restart',restart,'step',k,'seconds',time.time()-start,flush=True)
                (OUT/'macro_best.json').write_text(json.dumps(cur))
            if time.time()-start>150: return

if __name__=='__main__':main()
