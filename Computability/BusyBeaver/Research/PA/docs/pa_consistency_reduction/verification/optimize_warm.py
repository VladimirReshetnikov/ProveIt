#!/usr/bin/env python3
"""Anneal AX bracketings by nodes minus available predecessor-bit folds."""
import symbolic as S
from pathlib import Path
import sys,json,random,math,time,collections,re,functools
WORK=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(WORK/'math_reduction/grammar'))
from rotate_search import tree,nodes,paths,replace,replace_one,output,expand,WORD
from search_grammar import TOKENS

NM=json.loads((WORK/'verification/node_map.json').read_text())
ATOM={v:NM[k][0] for k,v in TOKENS.items()}|{'i':58}
FREE={('i','i'):87,(('i','i'),('i','i')):121}
BASE={k:v for k,v in S.load_machine().items()if k[0]<134}
RAW=S.source_tree()[1]
LEADING={};MAXRUN={}
for name,atom in TOKENS.items():
    pp=[''.join(map(str,p)) for p,op in S.flatten(RAW[name])]
    LEADING[atom]=max(len(x)-len(x.lstrip('0')) for x in pp)
    MAXRUN[atom]=max([0]+[len(z)for x in pp for z in re.findall('0+',x)])
LEADING.update(i=0,B=0);MAXRUN.update(i=0,B=0)
@functools.lru_cache(maxsize=200000)
def zero_shape(t):
    if isinstance(t,str):return LEADING[t],MAXRUN[t]
    la,ma=zero_shape(t[0]);lb,mb=zero_shape(t[1])
    return 1+la,max(1+la,ma,mb)


def evaluate(t):
    if zero_shape(t)[1]>9:return 1000,len(nodes(t)),0,[]
    new={};m=BASE.copy()
    def emit(x):
        if x in FREE:return FREE[x]
        if isinstance(x,str):return ATOM[x]
        if x in new:return new[x]
        a,b=x
        def row(y,bit):
            return (0,-1,131 if bit else 5) if y=='B' else (bit,1,emit(y))
        z0=row(a,0);z1=row(b,1)
        q=1000+len(new);new[x]=q;m[q,0]=z0;m[q,1]=z1
        return q
    entry=emit(t);m[89,1]=(1,1,entry)
    tags=collections.defaultdict(set)
    for (q,b),(w,d,r)in m.items():
        tags[r].update([w]if d==1 else [0,1])
    # The only context-sensitive macro root changed in the tested safe grammar.
    if any(x[0]=='G' or x[1] in ('R','S') for x in new):return 1000,len(new),0,[]
    pure={q for q,b in m if m[q,0][:2]==(0,1)and m[q,1][:2]==(1,1)}
    helpers=[{} for b in [0,1]]
    for b in [0,1]:
        for h in pure:
            v0=m[h,0][2];v1=m[h,1][2]
            if (v0,b)not in m or(v1,b)not in m:continue
            signature=m[v0,b],m[v1,b]
            helpers[b].setdefault(signature,[]).append((h,v0,v1))
    left=[q for q in new.values()if q in pure and tags[q]=={0}]
    right=[q for q in new.values()if q in pure and tags[q]=={1}]
    edges=collections.defaultdict(list);details=[]
    for q in left:
        for r in right:
            picks=[]
            for b in [0,1]:
                if m[q,b]==m[r,b]:picks.append(None);continue
                hs=[h for h,a,c in helpers[b].get((m[q,b],m[r,b]),[])if len({q,r,h,a,c})==5 or (q not in(h,a,c)and r not in(h,a,c))]
                if not hs:break
                picks.append(hs[0])
            else:edges[q].append(r);details.append((q,r,picks))
    mate={}
    def augment(q,seen):
        for r in edges[q]:
            if r in seen:continue
            seen.add(r)
            if r not in mate or augment(mate[r],seen):mate[r]=q;return True
        return False
    count=sum(augment(q,set())for q in left)
    return len(new)-count+max(0,zero_shape(t)[1]-6),len(new),count,details

def main():
    budget=int(sys.argv[1])if len(sys.argv)>1 else 30000
    rng=random.Random(963821)
    j=json.loads((Path(__file__).with_name('physical_60_119317.json')).read_text())
    def decode(n):return tuple(map(decode,j['rules'][n])) if n in j['rules'] else n
    base=decode(j['root']);bestt=base;best=evaluate(base)[0]
    t=base;score=best;start=time.monotonic()
    print('BASE',evaluate(base),flush=True)
    output(base,Path(__file__).with_name('physical_base.json'))
    seen={base};ties=[]
    for it in range(budget):
        if it%2000==0:t=rng.choice([base,bestt]+ties[-12:]);score=evaluate(t)[0]
        ps=paths(t);p,q=rng.choice(ps);a,b=q
        if rng.randrange(2):
            if not isinstance(a,tuple):continue
            u,v=a;alt=(u,(v,b))
        else:
            if not isinstance(b,tuple):continue
            u,v=b;alt=((a,u),v)
        cand=replace(t,q,alt)if rng.random()<.7 else replace_one(t,p,alt)
        if cand in seen:continue
        seen.add(cand)
        # Avoid spending the matcher on obvious cost excess.
        if len(nodes(cand))>78:continue
        s,n,c,ds=evaluate(cand)
        temp=.40*(1-(it%2000)/2000)+.08
        if s<1000 and (s<=score or rng.random()<math.exp((score-s)/temp)):
            t=cand;score=s
        if s<=best:
            if s<best:best=s;bestt=cand;print('BEST',best,n,c,'iteration',it,'seconds',round(time.monotonic()-start,1),flush=True)
            if len(ties)<200:ties.append(cand)
            if s<62:
                path=Path(__file__).with_name(f'warm_physical_{s}_{it}.json');output(cand,path)
                print('TARGET',path.name,ds,flush=True)
                if s<=60:break
        if it%1000==0:print('progress',it,'best',best,'current',score,'seconds',round(time.monotonic()-start,1),flush=True)
    print('DONE','best',best,'visited',len(seen),'seconds',round(time.monotonic()-start,1),flush=True)

if __name__=='__main__':main()
