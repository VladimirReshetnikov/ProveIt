"""Literal seed/interval oracle, independent of subset-layer derivation.
Checks each target's minimum partition against literal longest-prefix greedy,
then compares each slice maximum and the full cutoff to producer exact_rank.
Also classifies and tests all 72 directly enumerated rank-five NFAs.
"""
import itertools as it,json,sys,collections,pathlib
ROOT=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'producer'))
from exact_rank import exact_rank,slice_max,table,orbit

def rows(M,s):return tuple((M>>(i*s))&((1<<s)-1) for i in range(s))

def literal(s,A,B,I,F,N):
    # No viable layers: explicitly enumerate accepted seeds and their substrings.
    seeds=[]
    for w in it.product((0,1),repeat=N):
        active={i for i in range(s) if I>>i&1}
        for c in w:
            M=(A,B)[c]
            active={j for i in active for j in range(s) if M>>(s*i+j)&1}
        if any(F>>i&1 for i in active):seeds.append(w)
    if not seeds:return 0,0,None
    allowed={(i,j):{w[i:j] for w in seeds} for i in range(N) for j in range(i+1,N+1)}
    alph=[sorted({w[i] for w in seeds}) for i in range(N)]
    best=0;number=0;witness=None
    for w in it.product(*alph):
        # Actual minimum over every interval partition.
        cost=[0]+[N+1]*N
        for j in range(1,N+1):
            cost[j]=min(cost[i]+1 for i in range(j) if w[i:j] in allowed[i,j])
        # Greedy computed only from literal fragments, no NFA parser.
        boundary=0;ng=0
        while boundary<N:
            boundary=max(j for j in range(boundary+1,N+1) if w[boundary:j] in allowed[boundary,j]);ng+=1
        assert cost[N]==ng,(s,A,B,I,F,N,w,cost[N],ng)
        if cost[N]>best:best=cost[N];witness=''.join(map(str,w))
        number+=1
    return best,number,witness

def check(s,automata,extra):
    stat=collections.Counter();witnesses=[]
    for A,B,I,F in automata:
        r0,r1=rows(A,s),rows(B,s)
        result=exact_rank(s,r0,r1,I,F)
        horizon=result.get('horizon',7)+extra
        er=[x|y for x,y in zip(r0,r1)]
        rev=[sum(1<<u for u in range(s) if er[u]>>v&1) for v in range(s)]
        t,p,at,_=orbit(I,F,table(er),table(rev))
        observed=int(bool(I&F));first=None
        for N in range(1,horizon+1):
            val,nt,witness=literal(s,A,B,I,F,N)
            predicted=slice_max(N,I,F,[table(r0),table(r1)],at)[0]
            assert val==predicted,(s,A,B,I,F,N,val,predicted)
            stat['slices']+=1;stat['targets']+=nt
            if val>observed:observed=val;first=(N,witness)
        if result['finite']:assert observed==result['rank'],(s,A,B,I,F,result,observed)
        stat['automata']+=1
        if s==3:witnesses.append({'automaton':[A,B,I,F],'rank':observed,'first_maximum':first,'horizon':horizon})
    return dict(stat),witnesses

def conjugate(M,p):
    return sum(1<<(3*p[i]+p[j]) for i in range(3) for j in range(3) if M>>(3*i+j)&1)
def pset(Z,p):return sum(1<<p[i] for i in range(3) if Z>>i&1)
def orbit3(a):
    A,B,I,F=a
    return {b for p in it.permutations(range(3)) for b in ((conjugate(A,p),conjugate(B,p),pset(I,p),pset(F,p)),(conjugate(B,p),conjugate(A,p),pset(I,p),pset(F,p)))}

if __name__=='__main__':
    out={}
    out['two_state'],_=check(2,it.product(range(16),range(16),range(1,4),range(1,4)),1)
    (ROOT/'literal_receipt.json').write_text(json.dumps(out,indent=2))
    maxima=json.loads((ROOT/'independent_three_state.json').read_text())['maximizers']
    remaining=set(map(tuple,maxima));classes=[]
    while remaining:
        rep=min(remaining);orb=orbit3(rep);assert orb<=remaining
        classes.append({'representative':rep,'size':len(orb)})
        remaining-=orb
    out['maximizer_classes']=classes
    out['rank_five_automata'],witnesses=check(3,maxima,0)
    out['rank_five_witnesses']=witnesses
    out['passed']=True
    (ROOT/'literal_receipt.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='rank_five_witnesses'},indent=2))
