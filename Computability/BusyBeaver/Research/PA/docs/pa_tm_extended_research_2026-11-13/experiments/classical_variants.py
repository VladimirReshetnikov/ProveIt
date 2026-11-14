import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
"""Classical equivalent head presentations; h1 and rho8 remain unchanged."""
from core import *
from grammar import raw_nodes, axword
from layout import *
from collections import defaultdict, Counter
import random, time

ONE='1'
INC=('leaf','inc',1)
def I(a,b): return (0,a,b)
def M(a,b): return (1,a,b)
def U(a,b): return (2,b,a)
def E(a,b): return (3,a,b)
def N(a): return I(a,ONE)
def And(a,b): return N(I(a,N(b)))
def Ex(a,b): return N(U(a,N(b)))
def emit(f):
    if isinstance(f,str): return ['node49',INC] if f==ONE else [{'D':'node55','H':'node58','A':'node70'}[f]]
    tag,a,b=f
    return emit(a)+emit(b)+['node65']+[INC]*tag
def contra(f):
    assert f[0]==0
    return I(N(f[2]),N(f[1]))
def eq_variants(f):
    # Classical equivalences available once the unchanged h1 gives explosion.
    variants=[f]
    if isinstance(f,tuple) and f[0]==0:
        variants.append(contra(f))
        a,b=f[1:]
        if isinstance(b,tuple) and b[0]==0:
            variants += [I(b[1],I(a,b[2])), I(a,contra(b))]
            variants += [contra(x) for x in variants[2:]]
    return list(dict.fromkeys(variants))
d,h,a='DHA'
HEADS=[I(Ex(d,U(d,h)),h),I(U(d,U(a,h)),U(a,U(d,h))),
 I(M(h,d),I(E(h,a),M(a,d))), I(E(h,d),I(M(a,h),M(a,d))),
 Ex(d,E(h,d)), I(U(d,a),I(U(d,I(a,h)),U(d,h)))]
v=I(M(h,d),U(a,M(h,d)))
delta=I(E(h,d),U(a,E(h,d)))
p=I(a,M(a,d)); s=U(d,And(I(M(h,d),p),I(M(a,d),a)))
q=U(a,I(s,N(p)))
GATE=N(I(delta,I(v,q)))
word=axword(); blocks=[(x,int(y),int(z)) for x,y,z in re.findall(r'\(\.(\w+), (\d+), (\d+)\)',(ROOT/'PA196/Source/AXProgram.lean').read_text().split('def program')[0])]
ih=next(i for i,b in enumerate(blocks) if b[1]==503)
ig=next(i for i,b in enumerate(blocks) if b[1]==2258)
prefix=word[:ih];suffix=word[-3:]
assert sum(map(emit,HEADS),[])==word[ih:ig]
assert emit(GATE)==word[ig:-3]
raw=raw_nodes()
def expand(t):
    if isinstance(t,str) and t.startswith('x'):return tuple(expand(y) for y in raw[t])
    return t
initial=expand('x67')
trees=[]; ids={}; words=[]; masks=[]
def intern(t):
    if t in ids:return ids[t]
    if isnode(t):
        aa,bb=map(intern,t);ww=words[aa]+words[bb];mask=masks[aa]|masks[bb]
    else:ww=(t,);mask=0
    i=len(trees);trees.append(t);ids[t]=i;words.append(ww);masks.append(mask|(1<<i) if isnode(t) else 0)
    return i
intern(initial)
def parse(word,B=8):
    n=len(word);options=[]
    for i in range(n):
        options.append([j for j,w in enumerate(words) if tuple(word[i:i+len(w)])==w])
    dp=[{} for _ in range(n+1)];dp[0][0]=()
    for i in range(n):
        beam=sorted(dp[i].items(),key=lambda x:x[0].bit_count()+len(x[1]))[:B]
        dp[i]={}
        for mask,parts in beam:
            for j in options[i]:
                k=i+len(words[j]);mm=mask|masks[j];pp=parts+(j,)
                if mm not in dp[k] or len(pp)<len(dp[k][mm]):dp[k][mm]=pp
    mm,pp=min(dp[n].items(),key=lambda x:x[0].bit_count()+len(x[1]))
    return mm.bit_count()+len(pp)-1,pp
def encode(t):
    rs={};ii={}
    def rec(t):
        if not isnode(t):return t
        if t in ii:return ii[t]
        pair=list(map(rec,t));key='g'+str(len(rs));rs[key]=pair;ii[t]=key;return key
    rt=rec(t);return {'root':rt,'rules':rs}
def balanced(parts):
    if len(parts)==1:return parts[0]
    k=len(parts)//2;return balanced(parts[:k]),balanced(parts[k:])
if __name__=='__main__':
    opts=[[HEADS[0]]] + [eq_variants(f) if j!=4 else [f] for j,f in enumerate(HEADS[1:],1)]
    gates=[]
    for dv,vv in itertools.product([delta,contra(delta)],[v,contra(v)]):
        gates += [N(I(dv,I(vv,q))), N(I(vv,I(dv,q))), And(And(dv,vv),N(q)), And(N(q),And(dv,vv))]
    gates=list(dict.fromkeys(gates))
    start=time.monotonic();best=999;best_eff=999;found=[];hist=Counter()
    trials=list(itertools.product(*[range(len(x)) for x in opts],range(len(gates))))
    print('baseline',len(word),parse(word),'trials',len(trials),flush=True)
    for j,ix in enumerate(trials):
        fs=[opts[k][ix[k]] for k in range(6)];gate=gates[ix[-1]]
        ww=prefix+sum(map(emit,fs),[])+emit(gate)+suffix
        nn,pp=parse(ww);hist[nn]+=1
        if nn<best:
            best=nn;print('best',nn,'ix',ix,'tokens',len(ww),'elapsed',time.monotonic()-start,flush=True)
        if nn<=70:
            t=balanced([trees[z] for z in pp]);rr,idx,sh=build(t);ops=opportunities_fast(rr,sh);eff=len(sh)-len(max_matching(ops))
            rec={'cost':nn,'optimistic_effective':eff,'indices':ix,'tokens':len(ww),'parts':[encode(trees[z]) if isnode(trees[z]) else {'terminal':trees[z]} for z in pp]}
            found.append(rec)
            if eff<best_eff:best_eff=eff;print('effective',eff,ix,flush=True)
        if j%500==0:print('progress',j,'best',best,'seconds',time.monotonic()-start,flush=True)
    Path('classical_results.json').write_text(json.dumps({'best':best,'histogram':hist,'found':found},indent=2))
