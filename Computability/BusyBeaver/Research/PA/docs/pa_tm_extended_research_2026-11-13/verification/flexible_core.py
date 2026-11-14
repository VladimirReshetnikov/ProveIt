"""Reachability-aware symbolic physical screen with repeated box excursions.

The original engine rows must remain unchanged. Logical register offsets are
tracked; appended spare registers and extra positive-decrement gap growth are
allowed. This executable is not a Lean proof.
"""
import core
from core import *
from collections import defaultdict
import time
INV=Path(__file__).with_name('zero_invariants.json')
inv=json.loads(INV.read_text())
DBMS=[]
for ln in Path(__file__).with_name('dbm_certificate.txt').read_text().splitlines()[1:]:
    vv=list(map(int,ln.split()));DBMS.append(None if vv[1] else vv[2:])
REDUCED=Path(__file__).with_name('reduced_certificate.txt')
if REDUCED.exists():
    for ln in REDUCED.read_text().splitlines()[1:]:
        vv=list(map(int,ln.split()));pc=vv[0]
        DBMS[pc]=None if vv[1] else vv[2:102]
        inv['reachable_masks'][pc]=str(sum(x<<(64*k)for k,x in enumerate(vv[102:])))
def refine_dbm(i,br):
    if DBMS[i] is None:return None
    d=DBMS[i].copy()
    if br is not None:
        r=PHYSICAL.index(br[0]);k=10*r+9 if br[1] else 90+r
        d[k]=min(d[k],0 if br[1] else -1)
        for k in range(10):
            for a in range(10):
                if d[10*a+k]>=100000000:continue
                for b in range(10):
                    if d[10*k+b]<100000000:d[10*a+b]=min(d[10*a+b],d[10*a+k]+d[10*k+b])
        if any(d[11*a]<0 for a in range(10)):return None
    return d
DELTA=(0,)*9
def box(mark=-1,delta=DELTA,append=0):return ('x',mark,delta,append)
def update(delta,r,d):
    out=list(delta);out[r]+=d;return tuple(out)
def oracle_flex(q,br,x):
    _,mark,delta,append=x
    base,zero,positive,bounds=br
    if mark<0 and q in SKMAP:
        r=SKMAP[q];return (1 if r==0 else 3,box(r,delta,append),False)
    if 0<=mark<9:
        r=mark
        if q==64:return 40,box(-1,update(delta,r,1),append+1),False
        if q==0:
            lower,upper=bounds[r]
            if upper<100000000 and upper+delta[r]==0:
                return 97,box(-1,delta,append),False
            if lower+delta[r]>=1:
                return 40,box(-1,update(delta,r,-1),append),True
    return None
core.oracle=oracle_flex
def target_match(s,t):
    if s[0]!=t[0] or s[1]!=t[1] or norm(s[2],True)!=norm(t[2],True):return False
    rr,tt=norm(s[3]),norm(t[3])
    if len(rr)!=len(tt):return False
    for x,y in zip(rr,tt):
        if x[0]=='x' and y[0]=='x':
            if x[1]!=-1 or x[2]!=y[2]:return False
        elif x[0]=='r' and y[0]=='r' and x[1:3]==y[1:3]==(0,1):
            if x[3]<y[3]:return False
        elif x!=y:return False
    return True
def run_flex(rows,c,fuel=1600,observe=None):
    site,br,s,t=c;moved=False
    for k in range(fuel):
        if moved and (s[0]==254 if t is None else target_match(s,t)):return k
        if observe:observe(s)
        nxt=core.sstep(rows,br,s)
        if nxt is None:return None
        s,m=nxt;moved|=m
    return None
def flex_frame(p,delta=DELTA):
    return (84,False,(BIT[1],),tuple(BIT[b] for b in p)+(('r',0,1,48-len(p)),BIT[1],box(-1,delta)))
def flex_contracts():
    ss,ins=program();cs=[];omitted=[]
    for c in core.contracts():
        i,br,st,t=c;masks=int(inv['reachable_masks'][i])
        if not masks:omitted.append((i,br,'unreachable'));continue
        dd=refine_dbm(i,br)
        if dd is None:omitted.append((i,br,'DBM_unreachable'));continue
        ms=[m for m in range(512)if masks>>m&1]
        if br is not None:
            r=PHYSICAL.index(br[0]);ms=[m for m in ms if bool(m>>r&1)==(not br[1])]
            if not ms:omitted.append((i,br,'impossible_branch'));continue
        ms=[m for m in ms if all(not(m>>r&1) or (m>>s&1) for r in range(9) for s in range(9) if dd[10*r+s]<=0)
            and all(not(m>>r&1) for r in range(9) if dd[10*r+9]<=0)
            and all(m>>r&1 for r in range(9) if dd[90+r]<=-1)]
        if not ms:omitted.append((i,br,'product_unreachable'));continue
        zero=frozenset(PHYSICAL[r] for r in range(9) if dd[10*r+9]<=0 or all(not(m>>r&1)for m in ms))
        pos=frozenset(PHYSICAL[r] for r in range(9) if dd[90+r]<=-1 or all(m>>r&1 for m in ms))
        bounds=[None]*9
        for r in range(9):
            ph=PHYSICAL[r]
            lo=max(0,-dd[90+r],int(ph in pos))
            hi=min(dd[10*r+9],0 if ph in zero else 100000000)
            bounds[ph]=(lo,hi)
        code=ins[i];delta=DELTA
        if code[0]=='inc':
            delta=update(delta,PHYSICAL[code[1]],1);end=code[2]
        elif code[0]=='dec':
            if br[1]:end=code[2]
            else:delta=update(delta,PHYSICAL[code[1]],-1);end=code[3]
        elif code[0]=='jump':end=code[1]
        target=None if code[0]=='halt' else flex_frame(ss[end][0],delta)
        cs.append((i,(br,zero,pos,tuple(bounds)),flex_frame(ss[i][0]),target))
    return cs,omitted
def validate_flex(rows,cs):
    lengths=[]
    for c in cs:
        v=run_flex(rows,c)
        if v is None:return {'ok':False,'failed':(c[0],str(c[1])),'completed':len(lengths)}
        lengths.append(v)
    return {'ok':True,'contracts':len(cs),'max_steps':max(lengths),'total_steps':sum(lengths)}
def quotient(rows,a,b):return {(q,bit):(w,d,b if n==a else n)for(q,bit),(w,d,n)in rows.items()if q!=a}
if __name__=='__main__':
    rows,labels=machine();cs,om=flex_contracts();print('baseline',validate_flex(rows,cs),'omitted',om,flush=True)
    protected={(q,b)for q in BOXSTATES for b in [0,1]if (q,b) in rows and (q,b)!=(113,0)}
    states=sorted({q for q,b in rows});found=[];tried=0;start=time.monotonic()
    for a,b in itertools.permutations(states,2):
        rr=quotient(rows,a,b)
        if any(rr.get(x)!=rows[x]for x in protected):continue
        def act(q,bit):
            w,d,n=rows[q,bit];return w,d,b if n==a else n
        if not any(act(a,bit)==act(b,bit)for bit in [0,1]):continue
        tried+=1;ans=validate_flex(rr,cs)
        if ans['ok']:
            print('SURVIVOR',a,b,ans,flush=True)
            out={'rows':[[q,bit,*v]for(q,bit),v in sorted(rr.items())],'merge':[a,b],'validation':ans,'omitted':om}
            Path(f'flex_candidate_{a}_{b}.json').write_text(json.dumps(out,indent=2));found.append([a,b])
        if tried%50==0:print('progress',tried,time.monotonic()-start,flush=True)
    Path('flex_result.json').write_text(json.dumps({'tried':tried,'survivors':found,'elapsed':time.monotonic()-start},indent=2))
    print('DONE',tried,found,time.monotonic()-start,flush=True)
