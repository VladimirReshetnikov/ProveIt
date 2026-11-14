import grammar as g
from pathlib import Path
import random,collections,json,itertools,time
C='node65';i='inc1';P='node49';D='node55';H='node58';A='node70'
def I(a,b):return ('I',a,b)
def U(a,b):return ('S',('S',I(b,a)))
def M(a,b):return ('S',I(a,b))
def E(a,b):return ('S',('S',('S',I(a,b))))
def N(a):return I(a,1)
def ex(a,b):return N(U(a,N(b)))
def conj(a,b):return N(I(a,N(b)))
def compile(t):
    if t==1:return [P,i]
    if isinstance(t,str):return [t]
    if t[0]=='S':return compile(t[1])+[i]
    assert t[0]=='I';return compile(t[1])+compile(t[2])+[C]
heads=[I(ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
words=list(map(compile,heads))
prefix=g.seq[:18]
suffix=g.seq[18+sum(map(len,words)):]
assert prefix+sum(words,[])+suffix==g.seq
print('LENGTHS',len(prefix),[len(w) for w in words],len(suffix),flush=True)
# exact grammar size, symbols interned node IDs, initial atom IDs have no cost
leaves=list(g.atoms.values()); L=len(leaves)
def repair(s,seed):
    random.seed(seed)
    pairs={};defs=[];seq=[leaves.index(x) for x in s]
    # hash-cons always; merge frequent chosen pairs
    while len(seq)>1:
        counter=collections.Counter(zip(seq,seq[1:]))
        candidates=[(count-(0 if pair in pairs else 1)+random.uniform(0,1.5),random.random(),pair) for pair,count in counter.items() if count>1 or pair in pairs]
        if not candidates:break
        pair=max(candidates)[2]
        if pair not in pairs:pairs[pair]=L+len(defs);defs.append(pair)
        sym=pairs[pair];new=[];j=0
        while j<len(seq):
            if j+1<len(seq) and (seq[j],seq[j+1])==pair:new.append(sym);j+=2
            else:new.append(seq[j]);j+=1
        seq=new
    while len(seq)>1:
        j=random.randrange(len(seq)-1);pair=(seq[j],seq[j+1])
        if pair not in pairs:pairs[pair]=L+len(defs);defs.append(pair)
        seq[j:j+2]=[pairs[pair]]
    def expand(t):return g.nodes.get(leaves[t],leaves[t]) if t<L else tuple(map(expand,defs[t-L]))
    return len(defs),lambda:expand(seq[0])
