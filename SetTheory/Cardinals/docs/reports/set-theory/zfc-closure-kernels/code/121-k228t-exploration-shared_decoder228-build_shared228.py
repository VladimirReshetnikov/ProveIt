#!/usr/bin/env python3
"""Reconstruct the 228-state shared-decoder alternative, finite source and tape proofs.

The new layout has the same state count as the supplied K228 input. Source,
bootstrap and two local projection cases are proved here. Run code/verify_runtime_k.py
for the separate universal binary runtime theorem.
"""
from pathlib import Path
from functools import cache
from collections import defaultdict,Counter
import argparse,hashlib,json,sys
HERE=Path(__file__).resolve().parent
TABLE='2b791ed22523b9610d43d7440631b27063089d2d1a24cf3bfbe5ace6cf416ea2'
SOURCE='61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b'
RESULT='88060858ad3f89f42e401f5cb504c866f1e64a0a71a66bb83faab0576da6a4c8'
NEW_SOURCE='086978093606eff05089b1f115b58110f8b01900013677ec716c71ad4bed6d79'
def sha(x):return hashlib.sha256(x).hexdigest()
def require(x,msg):
    if not x:raise ValueError(msg)
def parse(raw):
    rows={};starts=[]
    for line in raw.decode().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b) not in rows and b in(0,1) and w in(0,1) and d in('L','R'),'Malformed row')
        rows[q,b]=(w,1 if d=='R' else -1,z)
    qs={q for q,b in rows}
    require(starts==[0] and qs==set(range(230))-{79,140},'Unexpected input states')
    require(set(rows)=={(q,b) for q in qs for b in(0,1)},'Incomplete table')
    require({z for w,d,z in rows.values()}-qs=={230},'Unexpected halt')
    return rows
def encode(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z) in sorted(t.items()))).encode()
def leaf(n):return isinstance(n[0],str)
def tree(rows):
    trie={}
    for p,o,r in rows:
        require(p and not(set(p)-{'0','1'}) and o in('CI','CD','CB','CC','CH'),'Source syntax')
        at=trie
        for bit in p:
            require('leaf' not in at,'Prefix collision');at=at.setdefault(bit,{})
        require(not at,'Duplicate source leaf');at['leaf']=(o,r)
    def visit(n):
        if 'leaf' in n:return n['leaf']
        require(set(n)=={'0','1'},'Source tree is not full');return visit(n['0']),visit(n['1'])
    return visit(trie)
def sites(t,p=''):
    return [(p,*t)] if leaf(t) else sites(t[0],p+'0')+sites(t[1],p+'1')
@cache
def boundary(t):
    if leaf(t):
        o,r=t;return (1,0,False) if o=='CD' else (r,0,False) if o=='CB' else (0,r,False) if o=='CC' else (0,0,o=='CH')
    a,b=map(boundary,t);return max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2] or b[2]
def source_map(root,t):
    inverse=defaultdict(set);seen=set()
    def visit(n,q):
        if leaf(n) or (n,q) in seen:return
        seen.add((n,q));inverse[q].add(n)
        for b in(0,1):
            w,d,z=t[q,b]
            if(w,d)==(b,1):visit(n[b],z)
    visit(root,84);return inverse
def replace(root,replacements):
    @cache
    def rec(n):return replacements[n] if n in replacements else n if leaf(n) else (rec(n[0]),rec(n[1]))
    return rec(root)
def graph(rows):
    ordered=sorted(tuple(x) for x in rows);leaves={p:i for i,(p,o,r) in enumerate(ordered)};mx=max(map(len,leaves))
    prefixes={p[:k] for p in leaves for k in range(len(p))}
    require(not(set(leaves)&prefixes) and all(p+c in prefixes or p+c in leaves for p in prefixes for c in'01'),'Malformed source')
    def locate(p):
        word=p+'0'*mx
        for k in range(1,mx+1):
            if word[:k] in leaves:
                require('1' not in p[k:],'Noncanonical successor suffix');return leaves[word[:k]]
        raise ValueError('Missing successor')
    def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b') if p else ''
    def cut(p,c,k):
        if k==0:return p
        pos=[i for i,b in enumerate(p) if b==c];return p[:pos[-k]] if len(pos)>=k else ''
    out=[]
    for p,o,r in ordered:
        if o=='CI':out.append(('INC',r,locate(inc(p))))
        elif o=='CD':out.append(('DEC',r,locate(inc(p)),locate(inc(cut(p,'0',1)))))
        elif o=='CB':out.append(('JUMP',locate(inc(cut(p,'0',r)))))
        elif o=='CC':out.append(('JUMP',locate(cut(p,'1',r))))
        else:out.append(('HALT',))
    return [r[1:] for r in ordered],out,locate('')
def metrics(root):
    live=set()
    def visit(n):
        if n in live:return
        live.add(n)
        if not leaf(n):visit(n[0]);visit(n[1])
    visit(root);ss=sites(root)
    return dict(dag_nodes=len(live),leaf_occurrences=len(ss),maximum_depth=max(len(p) for p,o,r in ss),maximum_zero_run=max(len(z) for p,o,r in ss for z in p.split('1')))
def projection(t,tag):
    tape={-1:tag,0:0};q=175;h=0;trace=[]
    for _ in range(3):
        require(h in tape,'Projection read exterior');b=tape[h];w,d,z=t[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
    require((q,h,tape)==((19 if tag==0 else 90),1,{-1:tag,0:0}),'Projection changed')
    return trace
def main():
    require(__debug__ and not sys.flags.optimize,'Enable assertions')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',type=Path,required=True);a=ap.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
    raw=(HERE/'inputs/k228_original_labels.tm').read_bytes();src=(HERE/'inputs/sites5121.json').read_bytes()
    require(sha(raw)==TABLE and sha(src)==SOURCE,'Pinned input bytes changed');old=parse(raw);ss=json.loads(src);root=tree(ss);inv=source_map(root,old)
    require(len(inv[85])==len(inv[65])==1,'Ambiguous decoder');n=next(iter(inv[85]));A,(B,C)=n
    require((B,C)==next(iter(inv[65])) and all(boundary(x)==(0,0,False) for x in(A,B,C)),'Nonclosed initial rotation')
    root=replace(root,{n:((A,B),C)});t=dict(old);t[85,0]=(0,1,65);t[85,1]=(1,1,12);t[65,0]=(0,1,19);t[65,1]=(1,1,114)
    require((t[65,0],t[65,1])==(t[98,0],t[98,1]),'Duplicate did not appear')
    t={(q,b):(w,d,98 if z==65 else z) for(q,b),(w,d,z) in t.items() if q!=65};inv=source_map(root,t);reps={};rotations=[]
    for q in(76,155):
        require(len(inv[q])==1,'Ambiguous shared parent');n=next(iter(inv[q]));(A,B),C=n
        require(all(boundary(x)==(0,0,False) for x in(A,B,C)),'Escaping shared rotation')
        reps[n]=(A,(B,C));rotations.append(dict(outer=q,chunk_leaf_counts=[len(sites(v)) for v in(A,B,C)]))
    root=replace(root,reps);ss2=sites(root);require(graph(ss)==graph(ss2),'Source graph changed')
    for q,z0,z1 in[(76,98,85),(85,12,86),(155,98,65),(65,12,175)]:t[q,0]=(0,1,z0);t[q,1]=(1,1,z1)
    t[175,0]=(0,-1,85);require(set(t)==set(old),'Working-state count changed')
    paths=[dict(tag=bit,old=projection(old,bit),new=projection(t,bit)) for bit in(0,1)]
    newraw=encode(t);newsrc=(json.dumps(ss2,separators=(',',':'))+'\n').encode();require(sha(newraw)==RESULT and sha(newsrc)==NEW_SOURCE,'Unexpected result bytes')
    changed={k for k in t if t[k]!=old[k]};q=0;h=0;ones=set();visits=Counter()
    for tick in range(409835):
        key=q,int(h in ones);require(key not in changed,'Changed bootstrap row');visits[key]+=1
        w,d,z=old[key]
        if w:ones.add(h)
        else:ones.discard(h)
        q=z;h+=d
    require((q,h,len(ones))==(84,-5,351),'Wrong bootstrap endpoint')
    receipt=dict(status='PASS_SOURCE_SHARED_ROTATIONS_DUPLICATE_REUSE_PROJECTION_AND_FULL_STARTUP',working_states=228,rows=456,source_sites=5121,guarded_cases=6656,metrics=metrics(root),baseline_sha256=TABLE,baseline_source_sha256=SOURCE,machine_sha256=RESULT,source_sha256=NEW_SOURCE,projection_cases=paths,shared_parent_rotations=rotations,bootstrap_steps=409835,bootstrap_matched_checkpoints=409836,bootstrap_changed_row_visits=0,bootstrap_endpoint=dict(state=q,head=h,ones=sorted(ones)),changed_rows=[dict(row=list(k),before=old[k],after=t[k]) for k in sorted(changed)],runtime_scope='Separate exact-table unary/list-induction proof required; supplied runtime evidence and checker quantify over unbounded valid frames.')
    (a.output_dir/'k228_shared.tm').write_bytes(newraw);(a.output_dir/'sites_shared.json').write_bytes(newsrc);(a.output_dir/'construction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in('projection_cases','bootstrap_endpoint','changed_rows')},indent=2))
if __name__=='__main__':main()
