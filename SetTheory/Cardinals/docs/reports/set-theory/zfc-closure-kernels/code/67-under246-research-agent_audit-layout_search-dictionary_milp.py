#!/usr/bin/env python3
"""Minimize a shared binary grammar with an explicit integer program.

Only association of closed sequential components is changed. The unchanged
control atoms retain their exact ordered children and loop-depth semantics.
"""
import sys,json,time,argparse
from pathlib import Path
from collections import Counter
from functools import lru_cache
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
import grammar_layout as g
HERE=Path(__file__).resolve().parent
b=g.rot.edge_bounds(g.original);interned={};labels={};cache={};oldsplit={}
def intern(k):
    if k not in interned:interned[k]=len(labels);labels[len(labels)]=k
    return interned[k]
def canonical(e):
    if e in cache:return cache[e]
    if e[0]!='N':v=intern(('L',e))
    else:
        a,c=g.original[e[1]];aa,cc=canonical(a),canonical(c)
        if b(a)[1:]==b(c)[1:]==(0,0):
            aw=labels[aa][1] if labels[aa][0]=='S' else (aa,)
            cw=labels[cc][1] if labels[cc][0]=='S' else (cc,)
            v=intern(('S',aw+cw));oldsplit[aw+cw]=(aw,cw)
        else:v=intern(('A',aa,cc))
    cache[e]=v;return v
canonical_root=canonical(('N',g.original_root))
oldwords={v[1] for v in labels.values() if v[0]=='S'}
required={labels[x][1] for k in labels.values() if k[0]=='A' for x in k[1:] if labels[x][0]=='S'}
if labels[canonical_root][0]=='S':required.add(labels[canonical_root][1])

grammar_kind='ordered_closed_association'
output_prefix='dictionary'
extra_words=set()
def normalize_word(w):return w
def split_word(w,dictionary):
    return [(w[:i],w[i:]) for i in range(1,len(w)) if (i==1 or w[:i] in dictionary) and (i==len(w)-1 or w[i:] in dictionary)]

def emit(selected):
    nodes={};pairs={}
    def pair(a,b):
        k=(a,b)
        if k not in pairs:pairs[k]=len(nodes);nodes[len(nodes)]=k
        return ('N',pairs[k])
    @lru_cache(None)
    def word(w):
        if len(w)==1:return sym(w[0])
        a,c=selected[w]
        assert normalize_word(a+c)==w
        return pair(word(a),word(c))
    @lru_cache(None)
    def sym(i):
        k=labels[i]
        if k[0]=='L':return k[1]
        if k[0]=='S':return word(k[1])
        return pair(sym(k[1]),sym(k[2]))
    r=sym(canonical_root)[1]
    return nodes,r

def shortzero_words():
    """Seed the dictionary with archival closed rebracketings.

    Only words in the original atom alphabet are retained.  This does not
    assume archival equivalence: the MILP still derives exactly the original
    required words by concatenation.
    """
    oldlabels=dict(labels);oldinterned=dict(interned);extra=set()
    archive=json.loads((g.BASE/'records/short-zero-layout.json').read_text())
    for candidate in archive['short_zero_layouts']:
        nn={int(i):tuple(map(tuple,p)) for i,p in candidate['nodes'].items()}
        bound=g.rot.edge_bounds(nn)
        @lru_cache(None)
        def visit(e):
            if e[0]!='N':return intern(('L',e))
            a,c=nn[e[1]];aa,cc=visit(a),visit(c)
            if bound(a)[1:]==bound(c)[1:]==(0,0):
                aw=labels[aa][1] if labels[aa][0]=='S' else (aa,)
                cw=labels[cc][1] if labels[cc][0]=='S' else (cc,)
                w=normalize_word(aw+cw)
                if all(i in oldlabels for i in w):extra.add(w)
                return intern(('S',w))
            return intern(('A',aa,cc))
        visit(('N',candidate['root']))
    labels.clear();labels.update(oldlabels)
    interned.clear();interned.update(oldinterned)
    return extra

def run(maxlen=0,minfreq=2,seconds=120,maxzeros=0,maxdepth=0,prefer_old=False,seed_shortzero=False,tm_price=False,freeze=()):
    words=set(oldwords)
    words.update(extra_words)
    if seed_shortzero:words.update(shortzero_words())
    freq=Counter(normalize_word(w[i:i+n]) for w in required for n in range(2,min(len(w),maxlen)+1) for i in range(len(w)-n+1))
    words.update(w for w,f in freq.items() if f>=minfreq)
    words=sorted(words,key=lambda w:(len(w),w));idx={w:i for i,w in enumerate(words)}
    splits={}
    for w in words:
        splits[w]=split_word(w,idx)
    # Repeatedly discard phrases that have no complete derivation in this
    # candidate dictionary; otherwise infeasible optional variables remain.
    possible=set()
    for w in words:
        splits[w]=[(a,c) for a,c in splits[w] if (len(a)==1 or a in possible) and (len(c)==1 or c in possible)]
        if splits[w]:possible.add(w)
    words=[w for w in words if w in possible];idx={w:i for i,w in enumerate(words)}
    assert required<=possible
    y={};nv=len(words)
    for w in words:
        for k in range(len(splits[w])):y[w,k]=nv;nv+=1
    controls=[i for i,k in labels.items() if k[0]=='A']
    entries={};entryvars={};controlentries=set()
    if tm_price:
        metadata=json.loads((g.BASE/'historical/decoder_entries.json').read_text())
        entries={int(i):int(max(v,key=v.get)) for i,v in metadata['state_entries'].items()}
        bylabel={v:e[1] for e,v in cache.items() if e[0]=='N'}
        controlentries={entries[bylabel[i]] for i in controls}
        entrywords={}
        for i,k in labels.items():
            if k[0]=='S':entrywords.setdefault(entries[bylabel[i]],[]).append(k[1])
        for q in entrywords:
            if q not in controlentries:entryvars[q]=nv;nv+=1
    z={};depth={}
    if maxzeros:
        for k in [('S',w) for w in words]+[('A',i) for i in controls]:z[k]=nv;nv+=1
    if maxdepth:
        for k in [('S',w) for w in words]+[('A',i) for i in controls]:depth[k]=nv;nv+=1
    data=[];rows=[];cols=[];lo=[];hi=[]
    def add(coeff,l,u):
        row=len(lo);lo.append(l);hi.append(u)
        for col,v in coeff.items():rows.append(row);cols.append(col);data.append(v)
    for w in words:
        add({idx[w]:-1,**{y[w,k]:1 for k in range(len(splits[w]))}},0,0)
        for k,(a,c) in enumerate(splits[w]):
            for child in set((a,c)):
                if len(child)>1:add({y[w,k]:1,idx[child]:-1},-np.inf,0)
    if tm_price:
        for q,qv in entryvars.items():
            group=[w for w in entrywords[q] if w in idx]
            for w in group:add({idx[w]:1,qv:-1},-np.inf,0)
            add({qv:1,**{idx[w]:-1 for w in group}},-np.inf,0)
    def ref(w):
        if len(w)>1:return ('S',w)
        i=w[0]
        return ('A',i) if labels[i][0]=='A' else None
    def controlref(i):
        k=labels[i]
        return ('A',i) if k[0]=='A' else ('S',k[1]) if k[0]=='S' else None
    for bound,variables,exact in ((maxzeros,z,True),(maxdepth,depth,False)):
        if not bound:continue
        M=bound+2
        for w in words:
            for k,(a,c) in enumerate(splits[w]):
                for child in ((a,) if exact else (a,c)):
                    coeff={variables['S',w]:1,y[w,k]:-M}
                    rr=ref(child)
                    if rr is not None:coeff[variables[rr]]=-1
                    add(coeff,1-M,np.inf)
                    if exact:
                        coeff[y[w,k]]=M
                        add(coeff,-np.inf,1+M)
        for i in controls:
            for child in (labels[i][1:2] if exact else labels[i][1:]):
                coeff={variables['A',i]:1};rr=controlref(child)
                if rr is not None:coeff[variables[rr]]=-1
                add(coeff,1,1 if exact else np.inf)
    objective=np.zeros(nv);objective[:len(words)]=1000 if prefer_old else 1
    if tm_price:
        for w in oldwords:
            if w in idx:objective[idx[w]]=0
        for i in entryvars.values():objective[i]=1000 if prefer_old else 1
    if prefer_old:
        for (w,k),i in y.items():objective[i]=int(splits[w][k]!=oldsplit.get(w))
    lower=np.zeros(nv);upper=np.ones(nv)
    for i in z.values():upper[i]=maxzeros
    for i in depth.values():upper[i]=maxdepth
    for w in required:lower[idx[w]]=1
    for node in freeze:
        k=labels[cache['N',node]]
        assert k[0]=='S',('Only closed sequence split decisions can be frozen',node)
        w=k[1];split=oldsplit[w]
        assert split in splits[w],('Frozen original split is unavailable',node)
        lower[y[w,splits[w].index(split)]]=1
    matrix=coo_matrix((data,(rows,cols)),shape=(len(lo),nv)).tocsc()
    matrix.indices=matrix.indices.astype(np.int32);matrix.indptr=matrix.indptr.astype(np.int32)
    print('MODEL',len(words),'phrases',nv,'variables',len(lo),'constraints',flush=True)
    started=time.monotonic()
    res=milp(objective,integrality=np.ones(nv),bounds=Bounds(lower,upper),constraints=LinearConstraint(matrix,lo,hi),options={'time_limit':seconds,'mip_rel_gap':0})
    record=dict(grammar_kind=grammar_kind,maxlen=maxlen,minfreq=minfreq,maxzeros=maxzeros,maxdepth=maxdepth,prefer_old=prefer_old,seed_shortzero=seed_shortzero,tm_price=tm_price,freeze=list(freeze),seconds=time.monotonic()-started,message=res.message,status=res.status,
        objective=res.fun if res.x is not None else None,phrase_count=len(words),variables=nv)
    if res.x is not None:
        chosen=np.rint(res.x).astype(int)
        assert max(abs(res.x-chosen))<1e-4
        assert np.all(matrix@chosen >= np.array(lo)-1e-7) and np.all(matrix@chosen<=np.array(hi)+1e-7)
        selected={w:splits[w][next(k for k in range(len(splits[w])) if chosen[y[w,k]])] for w in words if chosen[idx[w]]}
        n,r=emit(selected);metric=(len(n),*g.rot.zero_metrics(n,r))
        record.update(root=r,nodes=n,metrics=metric,selected=[dict(word=w,left=a,right=c) for w,(a,c) in selected.items()])
        print('RESULT',metric,'selected phrases',len(selected),'seconds',record['seconds'],flush=True)
    else:print('RESULT',record,flush=True)
    suffix=f'_zero{maxzeros}_depth{maxdepth}_old{int(prefer_old)}' if maxzeros or maxdepth or prefer_old else ''
    if seed_shortzero:suffix+='_seed'
    if tm_price:suffix+='_tm'
    if freeze:suffix+='_freeze'+'-'.join(map(str,freeze))
    (HERE/f'{output_prefix}_max{maxlen}_freq{minfreq}{suffix}.json').write_text(json.dumps(record,indent=2)+'\n')
    return record

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--maxlen',type=int,default=0);ap.add_argument('--minfreq',type=int,default=2);ap.add_argument('--seconds',type=float,default=120)
    ap.add_argument('--maxzeros',type=int,default=0);ap.add_argument('--maxdepth',type=int,default=0);ap.add_argument('--prefer-old',action='store_true')
    ap.add_argument('--seed-shortzero',action='store_true');ap.add_argument('--tm-price',action='store_true')
    ap.add_argument('--freeze',default='',help='Comma-separated original nodes whose exact split must remain')
    a=ap.parse_args();run(a.maxlen,a.minfreq,a.seconds,a.maxzeros,a.maxdepth,a.prefer_old,a.seed_shortzero,a.tm_price,tuple(map(int,a.freeze.split(','))) if a.freeze else ())
