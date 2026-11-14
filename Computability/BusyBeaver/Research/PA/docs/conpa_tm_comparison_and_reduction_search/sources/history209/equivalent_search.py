#!/usr/bin/env python3
from variant_search import *
from itertools import product

def get_dictionary():
    _,_,t=get_macro_tree();ct=Counter()
    def f(t):
        if isinstance(t,str):return
        ct[t]+=1;f(t[0]);f(t[1])
    f(t);W=word(t);d={word(n):n for n,v in ct.items() if v>1};d.update({c:c for c in set(W)})
    return d

def parse_with_dictionary(w,d):
    dp=[None]*(len(w)+1);dp[0]=[]
    for i in range(len(w)):
        if dp[i] is None:continue
        for s,v in d.items():
            if w.startswith(s,i):
                j=i+len(s);new=dp[i]+[v]
                if dp[j] is None or len(new)<len(dp[j]):dp[j]=new
    pieces=dp[-1]
    return len(pieces)-1+len(set().union(*(nodes(v) for v in pieces))),pieces

def swap_antecedents(t):
    assert t[0]=='I' and t[2][0]=='I'
    a=t[1];b=t[2][1];c=t[2][2]
    return I(b,I(a,c))

def balanced(pieces):
    if len(pieces)==1:return pieces[0]
    k=len(pieces)//2
    return (balanced(pieces[:k]),balanced(pieces[k:]))

def main():
    d=get_dictionary();prefix,hs,gate=parts()
    D,H,A='D','H','A'
    h1alt=I(N(H),U(D,N(U(D,H))))
    variants=[[hs[0],h1alt],[hs[1]],[hs[2],swap_antecedents(hs[2])],
              [hs[3],swap_antecedents(hs[3])],[hs[4]],
              [hs[5],swap_antecedents(hs[5])]]
    newgate=N(swap_antecedents(gate[1]))
    gates=[gate,newgate]
    best=68;outs=[];rng=random.Random(27823)
    for picks in product(*[range(len(v)) for v in variants]):
        nhs=[v[p] for v,p in zip(variants,picks)]
        for gi,ng in enumerate(gates):
            suffix=enc(ng)+'LGX'
            for order in permutations(range(6)):
                w=prefix+''.join(enc(nhs[i]) for i in order)+suffix
                cost,pieces=parse_with_dictionary(w,d)
                if cost<best:
                    best=cost;outs=[]
                    print('BEST',cost,'picks',picks,'gate',gi,'order',order,flush=True)
                if cost==best:
                    outs.append({'head_order':order,'picks':picks,'gate':gi,'pieces':pieces,'word':w})
    (OUT/'equivalent_dp_best.json').write_text(json.dumps(outs))
    print('BESTS',best,len(outs),flush=True)
    # Run ordinary RePair on promising nontrivial variants, save every raw <=68.
    for idx,info in enumerate(outs):
        for j in range(16):
            t=repair(info['word'],rng,0 if j%2 else rng.randrange(1,6));c=count(t)
            if c<best:
                best=c
                print('REPAIR BEST',c,'info',idx,flush=True)
                (OUT/f'equiv_repair_best_{c}.json').write_text(json.dumps(dict(info,tree=t)))
    print('DONE',best,flush=True)

if __name__=='__main__':main()
