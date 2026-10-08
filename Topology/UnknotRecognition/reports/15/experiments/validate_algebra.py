#!/usr/bin/env python3
"""Exact exhaustive algebra checks; no numerical approximations."""
import sys, json, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'tests')]
from radical import *
from fixtures import *


def insert(pivots, x):
    while x:
        t=x.bit_length()-1
        if t not in pivots:
            pivots[t]=x
            return
        x ^= pivots[t]


def radical_layers(alg, ids):
    rad={(a,b):[1 << s for s in range(1 << alg.basis(a,b)[1])
                 if a!=b or s!=0] for a in ids for b in ids}
    current={key:vals[:] for key,vals in rad.items()}
    layers=[sum(1 << alg.basis(a,b)[1] for a in ids for b in ids),
            sum(map(len,current.values()))]
    k=len(alg.pairs[ids[0]])
    for _ in range(2,2*k+1):
        nxt={}
        for a in ids:
            for c in ids:
                span={}
                for b in ids:
                    for f in current[(a,b)]:
                        for g in rad[(b,c)]:
                            insert(span,alg.compose(a,b,c,f,g))
                nxt[a,c]=list(span.values())
        layers.append(sum(map(len,nxt.values())))
        current=nxt
    assert layers[-1]==0 and layers[-2]>0
    return layers


def main():
    started=time.perf_counter()
    counts={'monomial_products':0,'derivation_identities':0,'weight_identities':0,
            'sharp_words':0,'sharp_transfer_certificates':0,'random_transfer_certificates':0,
            'minimal_profiles':0}
    result={'status':'running','radical_layers':{},'counts':counts}
    for k in range(1,5):
        alg=ArcAlgebra()
        ids=[alg.intern(m) for m in matchings(tuple(range(2*k)))]
        result['radical_layers'][str(k)]=radical_layers(alg,ids)
        if k<=3:
            for a in ids:
                for b in ids:
                    for c in ids:
                        for s in range(1 << alg.basis(a,b)[1]):
                            for t in range(1 << alg.basis(b,c)[1]):
                                f,g=1<<s,1<<t
                                fg=alg.compose(a,b,c,f,g)
                                lhs=derivative(fg)
                                rhs=alg.compose(a,b,c,derivative(f),g)^alg.compose(a,b,c,f,derivative(g))
                                assert lhs==rhs
                                assert not fg or alg.weights(a,c,fg)=={next(iter(alg.weights(a,b,f)))+next(iter(alg.weights(b,c,g)))}
                                counts['monomial_products']+=1
                                counts['derivation_identities']+=1
                                counts['weight_identities']+=1
    result['sharp_depths']=[]
    for k in range(1,13):
        alg=ArcAlgebra()
        path,factors=sharp_word(alg,k)
        assert len(factors)==2*k-1
        assert word_product(alg,path,factors)==1 << ((1<<k)-1)
        counts['sharp_words']+=1
        if k<=8:
            d=sharp_transfer_complex(alg,k)
            t=transfer(d,alg,certificate=True)
            check_contraction(t,alg)
            assert len(t.d.src)==2
            assert t.d.cols[0].get(1)==1 << ((1<<k)-1)
            assert t.series_depth==2*k-2
            counts['sharp_transfer_certificates']+=1
            result['sharp_depths'].append({'k':k,'objects':len(d.src),'survivors':2,'series_depth':t.series_depth})
    for seed in range(500):
        k=seed%5
        alg=ArcAlgebra()
        d=gauge_complex(alg,k,seed,pairs=2+seed%5,survivors=seed%6,moves=12+seed%13)
        t=transfer(d,alg,certificate=True)
        check_contraction(t,alg)
        reference=pivot_reduce(d,alg)
        assert survivor_profile(d)==survivor_profile(reference)==survivor_profile(t.d)
        assert len(reference.src)==len(t.d.src)
        counts['random_transfer_certificates']+=1
        counts['minimal_profiles']+=1
    result.update(status='passed',seconds=time.perf_counter()-started)
    (ROOT/'results'/'algebra_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
