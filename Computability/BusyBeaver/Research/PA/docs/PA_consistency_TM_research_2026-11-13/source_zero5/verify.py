#!/usr/bin/env python3
"""Two source-CFG resolvers check the max-five-zero source witness.

This checks a source graph identity. It constructs no physical Turing machine.
"""
from pathlib import Path
import hashlib,json,re

ROOT=Path(__file__).resolve().parent
SOURCE_SHA='8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872'
OPS={'inc':'CI','dec':'CD','continueTo':'CC','breakTo':'CB','halt':'CH'}

def original(raw):
    env={};token=re.compile(r'\s*(\.leaf \(\.(?:inc|dec|continueTo|breakTo) \d+\)|\.leaf \(\.halt\)|[A-Za-z]\w*)')
    def atom(s):
        if not s.startswith('.leaf'): return env[s]
        m=re.fullmatch(r'\.leaf \(\.(\w+)(?: (\d+))?\)',s)
        if not m:raise ValueError('bad leaf')
        return OPS[m[1]],None if m[2] is None else int(m[2])
    for name,line in re.findall(r'^def (\w+) : Tree := \.node (.+)$',raw.decode(),re.M):
        args=token.findall(line)
        if len(args)!=2:raise ValueError('bad source node')
        env[name]=(atom(args[0]),atom(args[1]))
    roots=re.findall(r'^def trie : Tree := (\w+)\s*$',raw.decode(),re.M)
    if len(roots)!=1:raise ValueError('bad trie declaration')
    return env[roots[0]]

def leaf(t):return isinstance(t[0],str)
def leaves(t,p=''):
    if leaf(t):yield [p,*t]
    else:
        yield from leaves(t[0],p+'0');yield from leaves(t[1],p+'1')

def parse(rows):
    by={p:(o,a)for p,o,a in rows}
    if len(by)!=len(rows):raise ValueError('duplicate paths')
    prefixes={p[:j]for p in by for j in range(len(p)+1)}
    def rec(p):
        if p in by:
            if p+'0'in prefixes or p+'1'in prefixes:raise ValueError('leaf is also internal')
            return by[p]
        if p+'0'not in prefixes or p+'1'not in prefixes:raise ValueError('incomplete tree')
        return rec(p+'0'),rec(p+'1')
    tree=rec('')
    if list(leaves(tree))!=rows:raise ValueError('rows not in source order')
    return tree

def graph_by_prefix(rows):
    ps={p:i for i,(p,_,_) in enumerate(rows)}
    def locate(p):
        while p not in ps:p+='0'
        return ps[p]
    def after(p):
        j=p.rfind('0')
        return None if j<0 else locate(p[:j]+'1')
    def cut(p,bit,k):
        hits=[j for j,c in enumerate(p)if c==bit]
        if k>len(hits):raise ValueError('escaping jump')
        return p if k==0 else p[:hits[-k]]
    result=[]
    for p,o,a in rows:
        if o=='CI':result.append((o,a,after(p)))
        elif o=='CD':result.append((o,a,after(cut(p,'0',1)),after(p)))
        elif o=='CB':result.append(('J',after(cut(p,'0',a))))
        elif o=='CC':result.append(('J',locate(cut(p,'1',a))))
        elif o=='CH':result.append((o,))
        else:raise ValueError('unknown operation')
    return result

def graph_by_intervals(t):
    spans={};count=0
    def visit(x,p):
        nonlocal count
        start=count
        if leaf(x):count+=1
        else:visit(x[0],p+'0');visit(x[1],p+'1')
        spans[p]=(start,count)
    visit(t,'');rows=list(leaves(t));result=[]
    for i,(p,o,a)in enumerate(rows):
        forward=[spans[p[:j]][1]for j,c in enumerate(p)if c=='0'][::-1]
        backward=[spans[p[:j]][0]for j,c in enumerate(p)if c=='1'][::-1]
        def end(v):return None if v==count else v
        if o=='CI':result.append((o,a,end(i+1)))
        elif o=='CD':result.append((o,a,end(forward[0]),end(i+1)))
        elif o=='CB':result.append(('J',end(forward[a-1])))
        elif o=='CC':result.append(('J',backward[a-1]))
        elif o=='CH':result.append((o,))
        else:raise ValueError('unknown operation')
    return result

def metrics(t):
    internal=set()
    def scan(x):
        if not leaf(x)and x not in internal:
            internal.add(x);scan(x[0]);scan(x[1])
    scan(t);rows=list(leaves(t))
    return {'sites':len(rows),'internal_nodes':len(internal),'max_path':max(len(p)for p,_,_ in rows),
            'max_zero_run':max(max(map(len,p.split('1')))for p,_,_ in rows),'seed25_path':rows[25][0]}

def main():
    raw=(ROOT/'OriginalProgram.lean').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=SOURCE_SHA:raise ValueError('upstream source hash mismatch')
    old=original(raw);rows=json.loads((ROOT/'source159_zero5.json').read_text());new=parse(rows)
    old_rows=list(leaves(old))
    if [(op,arg) for _,op,arg in old_rows] != [(op,arg) for _,op,arg in rows]:
        raise ValueError('ordered primitive instruction word changed')
    go=graph_by_prefix(old_rows);gn=graph_by_prefix(rows)
    if go!=graph_by_intervals(old)or gn!=graph_by_intervals(new):raise ValueError('independent resolvers disagree')
    if go!=gn:raise ValueError('source control graph changed')
    oldm,newm=metrics(old),metrics(new)
    if oldm!={'sites':3812,'internal_nodes':159,'max_path':38,'max_zero_run':6,'seed25_path':'100000'}:raise ValueError(oldm)
    if newm['sites']!=3812 or newm['internal_nodes']!=159 or newm['max_zero_run']!=5:raise ValueError(newm)
    # Negative control: a changed increment operand must change the graph.
    changed=[r[:]for r in rows];i=next(i for i,r in enumerate(changed)if r[1]=='CI');changed[i][2]=(changed[i][2]+1)%9
    if graph_by_prefix(changed)==go:raise ValueError('mutation was not rejected')
    receipt={'status':'SOURCE_CFG_IDENTITY_PASS','original':oldm,'candidate':newm,
             'candidate_sha256':hashlib.sha256((ROOT/'source159_zero5.json').read_bytes()).hexdigest(),
             'rows_compared':len(go),'ordered_primitive_word_equal':True,
             'independent_resolvers':2,'mutation_rejected':True,
             'original_paths_containing_six_zeros':sum('000000' in p for p,_,_ in leaves(old)),
             'candidate_paths_containing_six_zeros':sum('000000' in p for p,_,_ in rows),
             'scope':'Exact finite source graph identity only; no new physical machine, startup, or PA consistency endpoint.'}
    (ROOT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
