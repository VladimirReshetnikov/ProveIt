#!/usr/bin/env python3
from repair_search import *
from itertools import permutations

def I(a,b):return ('I',a,b)
def M(a,b):return ('M',a,b)
def U(a,b):return ('U',a,b)
def E(a,b):return ('E',a,b)
def N(a):return I(a,'1')
def ex(a,b):return N(U(a,N(b)))
def conj(a,b):return N(I(a,N(b)))
def enc(x):
    if isinstance(x,str):return 'Pi' if x=='1' else x
    op,a,b=x
    if op=='U':return enc(b)+enc(a)+'Cii'
    return enc(a)+enc(b)+'C'+('i'*{'I':0,'M':1,'E':3}[op])

def subst(t,rep):
    if isinstance(t,str):return rep.get(t,t)
    return (t[0],subst(t[1],rep),subst(t[2],rep))

def parts():
    D,H,A='D','H','A'
    hs=[I(ex(D,U(D,H)),H),
        I(U(D,U(A,H)),U(A,U(D,H))),
        I(M(H,D),I(E(H,A),M(A,D))),
        I(E(H,D),I(M(A,H),M(A,D))),
        ex(D,E(H,D)),
        I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
    eq=I(E(H,D),U(A,E(H,D)))
    mv=I(M(H,D),U(A,M(H,D)))
    point=I(A,M(A,D))
    sep=U(D,conj(I(M(H,D),point),I(M(A,D),A)))
    q=U(A,I(sep,N(point)))
    gate=N(I(eq,I(mv,q)))
    prefix='HDCiiJHDCKDHCAHCCC'
    return prefix,hs,gate

def main():
    ns,mac,base=get_macro_tree(); baseword=word(base)
    prefix,hs,gate=parts();suffix=enc(gate)+'LGX'
    assert prefix+''.join(map(enc,hs))+suffix==baseword
    print('HEADS',list(map(enc,hs)), 'prefix',prefix,'suffix',suffix,flush=True)
    rng=random.Random(21941);best=68;bestcost=54;start=time.time();cnt=0
    orders=list(permutations(range(6)));rng.shuffle(orders)
    for order in orders:
        s=prefix+''.join(enc(hs[i]) for i in order)+suffix
        for j in range(16):
            t=repair(s,rng,0 if j%2 else rng.randrange(1,6));c=count(t);cnt+=1
            if c<best:
                best=c
                print('BEST DAG',c,'potential',overlay_potential(t),'order',order,'i',cnt,'sec',time.time()-start,flush=True)
                (OUT/f'variant_best_{c}.json').write_text(json.dumps({'tree':t,'head_order':order,'head_relabel':[]}))
            if c<=best+2:
                cost=c-overlay_potential(t)
                if cost<bestcost:
                    bestcost=cost
                    print('BEST FOLD',c,overlay_potential(t),cost,'order',order,'i',cnt,'sec',time.time()-start,flush=True)
                    (OUT/f'variant_fold_{cost}.json').write_text(json.dumps({'tree':t,'head_order':order,'head_relabel':[]}))
    letters=list(permutations('ADH'))
    for k in range(16000):
        order=rng.choice(orders)
        reps=[dict(zip('ADH',rng.choice(letters))) for _ in hs]
        nhs=[subst(h,rep) for h,rep in zip(hs,reps)]
        s=prefix+''.join(enc(nhs[i]) for i in order)+suffix
        t=repair(s,rng,0 if k%2 else rng.randrange(1,6));c=count(t);cnt+=1
        if c<best:
            best=c
            print('BEST DAG',c,'potential',overlay_potential(t),'order',order,'i',cnt,'sec',time.time()-start,flush=True)
            (OUT/f'variant_best_{c}.json').write_text(json.dumps({'tree':t,'head_order':order,'head_relabel':reps}))
        if c<=best+2:
            cost=c-overlay_potential(t)
            if cost<bestcost:
                bestcost=cost
                print('BEST FOLD',c,overlay_potential(t),cost,'order',order,'i',cnt,'sec',time.time()-start,flush=True)
                (OUT/f'variant_fold_{cost}.json').write_text(json.dumps({'tree':t,'head_order':order,'head_relabel':reps}))
    print('DONE',cnt,'best',best,'bestpotential',bestcost,flush=True)

if __name__=='__main__':main()
