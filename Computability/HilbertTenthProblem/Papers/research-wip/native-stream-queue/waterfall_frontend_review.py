"""Portable independent Waterfall frontend/common-column audit of pinned sources.

verify(root) reads the extracted waterfall-diophantine package, writes nothing,
and imports no author source. Author command replay is a separate recorded step.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import argparse, hashlib, json, math, random, re

PINS = {
 'SHA256SUMS':'9f82c14406ef9b404594492ab87f5028c74e8c0bd350e99db64c465d2980561b',
 'source/UniversalTM15x2.tm.txt':'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae',
 'source/UniversalTM15x2.twm.txt':'52cfed3f6cba671ed7b166c126288d555ed687b74622ae5a9aaa5bee1345e46a',
 'replay/verify_frontend.py':'951c3482067c6754f23f3ad4cf21e13efe32f51ec9eed599bce02cac6117589d',
 'replay/verify_frontend_independent.py':'d8956977d1d302004573ae9e162f929fa144026a464b6524d84a18a16f10531b',
 'replay/verify_matrix_definition.py':'acdbfaf3dc3d5199b97dab6b1fabdcca741313c6d13a9fe6de45589db5ce34e6',
 'replay/verify_certificates.py':'3e20a9820c442199f595c6dd7d5a5c74f0d9bc863d88fd2ca432d1452dc40f58',
 'paper/waterfall-diophantine.tex':'22d6fc7aa755dcd3f6043f1b7472a82f6df2221bc3b21582a9c0fa76372a4e2f',
 'paper/affine-gap-table.tex':'fcc548e40f23211f8150a4dda7dd961986309d953cbe362be3dc3d36a13cdf1f',
}
# Independently read from the rendered primary Table 16, PDF page 17.
C = 'cR2 bR3 cL7 cL6 bR1 bL4 cL8 bL9 cR1 bL11 cR12 cR13 cL2 cL3 cR14'.split()
B = 'bR1 bR1 cL5 bL5 bL4 bL4 bL7 bL7 bL10 --- bR14 bR12 bR12 cR15 bR14'.split()
NAMES = ['LT','Lt','Lu','Ld0','Ld1','Lm','Lw0','Lw1']
NAMES += [f'{q}:{s}' for q in range(15) for s in range(2)]
NAMES += ['Rw0','Rw1','Rm','Rd0','Rd1','Ru','Rt','RT']
INDEX = {v:i for i,v in enumerate(NAMES)}
H = INDEX['9:1']


def add(a,b): return tuple(x+y for x,y in zip(a,b))
def mul(a,k): return tuple(x*k for x in a)
def sub(a,b): return add(a,mul(b,-1))
def const(x): return (x,0,0)
def val(a,q,y): return a[0]+a[1]*q+a[2]*y


def canonical(q,s,L,R):
    a = [const(2) for _ in NAMES]
    a[INDEX['LT']] = add(const(2),mul(L,2))
    a[INDEX['RT']] = add(const(2),mul(R,2))
    for side in 'LR':
        for t in range(2): a[INDEX[side+'d'+str(t)]] = const(2+(s!=t))
    for u,t in product(range(15),range(2)):
        a[INDEX[f'{u}:{t}']] = const(1+(q!=u)+(s!=t))
    return a


def blocks(q,s,r,rule):
    w,D,qn = rule; O = 'R' if D=='L' else 'L'
    z = [([f'{q}:{s}'],const(1)),([D+'d0',D+'d1'],(0,1,0))]
    if r: z.append(([D+'d0'],const(1)))
    z += [([D+'T'],const(1)),([D+'u'],(0,1,0)),([D+'t'],const(1)),
          ([O+'m'],(0,0,1)),([O+'T'],const(1)),([O+'u'],(0,0,2)),
          ([O+'t'],const(1)),([O+'w'+str(w)],const(1))]
    return [([INDEX[x] for x in word],times) for word,times in z]


def event(d,M,h):
    t=min(d); ids=[i for i,v in enumerate(d) if v==t]
    if len(ids)>1:return 'tie',None,t
    i=ids[0]
    if i==h:return 'halt',i,t
    return 'fire',i,t


def run(a,M,h,limit):
    d=list(a); p=[0]*len(a); trace=[]
    for _ in range(limit+1):
        status,i,t=event(d,M,h)
        if status!='fire':return status,p,t,trace
        if len(trace)==limit:return 'cutoff',p,None,trace
        trace.append((i,t));p[i]+=1;d=[x+M[j][i] for j,x in enumerate(d)]


def verify(root):
    if not __debug__:raise RuntimeError('Assertions must be enabled for this development checker')
    root=Path(root); counts=Counter()
    for path,digest in PINS.items():
        assert hashlib.sha256((root/path).read_bytes()).hexdigest()==digest,path
    inventory={}
    for line in (root/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split(None,1);name=name.lstrip('*')
        path=root/name
        assert path.resolve().is_relative_to(root.resolve())
        raw_member=path.read_bytes();assert hashlib.sha256(raw_member).hexdigest()==digest
        inventory[name]={'sha256':digest,'bytes':len(raw_member)}
    inventory['SHA256SUMS']={'sha256':PINS['SHA256SUMS'],'bytes':(root/'SHA256SUMS').stat().st_size}
    assert len(inventory)==31
    counts['authenticated_original_members']=len(inventory)
    raw=json.loads((root/'source/UniversalTM15x2.twm.txt').read_text())
    assert len(raw)==47 and all(len(r)==47 for r in raw)
    assert raw[0]==[47]+[46]*46
    M=[[raw[i+1][j+1] for i in range(46)] for j in range(46)]
    assert all(type(x) is int and x>=0 for row in raw for x in row)
    assert max(map(max,M))==12 and all(M[H][i]>=0 for i in range(46))
    assert all(M[j][H]==0 for j in range(46)) and all(M[i][i]>0 for i in range(46) if i!=H)
    assert [r[0] for r in raw[1:]]==[a[0] for a in canonical(0,0,const(0),const(0))]
    rules={}
    source=(root/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0].split('_')
    for q,s in product(range(15),range(2)):
        p=(C,B)[s][q]
        rules[q,s]=None if p=='---' else (int(p[0]=='b'),p[1],int(p[2:])-1)
        expected='---' if p=='---' else str(int(p[0]=='b'))+p[1]+chr(64+int(p[2:]))
        assert source[q][3*s:3*s+3]==expected
        counts['primary_table_cells']+=1

    # Reconstruct all columns directly from Appendix A, in destination/source
    # convention, then compare with the independently transposed source bytes.
    rebuilt=[[0]*46 for _ in range(46)]
    def put(name,default,changes):
        col={n:default for n in NAMES};col.update(changes)
        for target,value in col.items():rebuilt[INDEX[target]][INDEX[name]]=value
    for D in 'LR':
        O='R' if D=='L' else 'L'
        put(D+'T',0,{D+'T':10,D+'m':9,D+'d0':9,D+'d1':9})
        put(D+'t',0,{D+'t':8,D+'u':7})
        put(D+'u',2,{D+'T':4,D+'t':0})
        put(D+'m',2,{D+'T':0,D+'t':6})
        for s in range(2):
            changes={D+'T':0,D+'t':2+2*s}
            for O2,t in product('LR',range(2)):changes[O2+'d'+str(t)]=3 if t==s else 1
            for q,t in product(range(15),range(2)):changes[f'{q}:{t}']=3 if t==s else 1
            put(D+'d'+str(s),2,changes)
            put(D+'w'+str(s),9,{D+'w'+str(s):11,O+'m':0,D+'T':5+2*s,D+'t':5,D+'u':5,D+'m':5,D+'d0':0,D+'d1':0})
    for (q,s),rule in rules.items():
        if rule is None:continue
        w,D,qn=rule;O='R' if D=='L' else 'L'
        changes={D+'T':0,D+'t':2,D+'u':3,D+'m':10,O+'T':4,O+'t':6,O+'u':7,O+'m':5}
        for t in range(2):
            alpha=int(t==s)-int(t==0)
            changes[D+'d'+str(t)]=1+alpha;changes[O+'d'+str(t)]=10+alpha
            changes[D+'w'+str(t)]=10;changes[O+'w'+str(t)]=10-2*int(t==w)
            for u in range(15):changes[f'{u}:{t}']=10-int(u==qn)+int(u==q)+alpha
        assert len(changes)==46
        put(f'{q}:{s}',0,changes)
    assert rebuilt==M;counts['matrix_entries']=46**2
    weights=[288 if name in ('Lu','Ru') else -373 if len(name)==3 and name[1]=='d'
             else 970 if name in ('Lm','Rm') else -4 if len(name)==3 and name[1]=='w' else 0 for name in NAMES]
    assert sum(weights)==1008
    for q,s in product(range(15),range(2)):
        state=canonical(q,s,(0,1,0),(0,0,1))
        assert tuple(sum(w*a[k] for w,a in zip(weights,state)) for k in range(3))==(1270,0,0)
        counts['canonical_potential_identities']+=1
    for i,name in enumerate(NAMES):
        assert sum(w*M[j][i] for j,w in enumerate(weights))==(0 if i==H else 2016+7056*int(':' in name))
        counts['trigger_potential_identities']+=1

    forms=Counter();Q,Y=(0,1,0),(0,0,1)
    for (q,s),rule in rules.items():
        if rule is None:continue
        w,D,qn=rule
        for r in range(2):
            X=add(mul(Q,2),const(r));L,R=(X,Y) if D=='L' else (Y,X)
            start=canonical(q,s,L,R);fired=[const(0) for _ in NAMES]
            for word,K in blocks(q,s,r,rule):
                qmin=int(K[1]>0);ymin=int(K[2]>0)
                total=[word.count(i) for i in range(46)]
                prefix=[0]*46
                for i in word:
                    for ell in ([const(0)] if K==const(1) else [const(0),sub(K,const(1))]):
                        n=[add(fired[u],add(const(prefix[u]),mul(ell,total[u]))) for u in range(46)]
                        for j in range(46):
                            if j==i:continue
                            gap=sub(start[j],start[i])
                            for u in range(46):gap=add(gap,mul(n[u],M[j][u]-M[i][u]))
                            assert val(gap,qmin,ymin)>=1 and gap[1]>=0 and gap[2]>=0
                            forms[gap,qmin,ymin]+=1;counts['strict_endpoint_obligations']+=1
                    prefix[i]+=1
                fired=[add(v,mul(K,total[i])) for i,v in enumerate(fired)]
            final=[add(start[j],tuple(sum(M[j][i]*fired[i][v] for i in range(46)) for v in range(3))) for j in range(46)]
            target=canonical(qn,r,Q,add(mul(Y,2),const(w))) if D=='L' else canonical(qn,r,add(mul(Y,2),const(w)),Q)
            shift=(19+2*r,6,6)
            assert all(sub(a,b)==shift for a,b in zip(final,target))
            assert tuple(sum(f[v] for f in fired) for v in range(3))==(6+r,3,3)
            counts['macrostep_identities']+=1;counts['final_coordinate_identities']+=46
    supplied=json.loads((root/'replay/affine-gap-forms.json').read_text())
    assert forms==Counter({((x['c'],x['a'],x['b']),x['Q_min'],x['Y_min']):x['multiplicity'] for x in supplied})
    tab=[]
    for line in (root/'paper/affine-gap-table.tex').read_text().splitlines():
        if re.match(r'^\d+ &',line):
            values=list(map(int,re.findall(r'\d+',line)));assert len(values)==12
            tab += [tuple(values[:6]),tuple(values[6:])]
    assert Counter(tab)==Counter((q,y,val(g,q,y),g[1],g[2],n) for (g,q,y),n in forms.items())
    counts['shifted_appendix_forms']=len(tab)

    # Select events by the actual minimum, never the prescribed block word.
    # Keep a separate one-cell tape map as the machine interpreter.
    rng=random.Random(460215)
    for (q,s),rule in rules.items():
        if rule is None:continue
        w,D,qn=rule
        for L,R in [(0,0),(1,0),(0,1),(1,1),(12,19),(257,0),(0,128)]+[(rng.randrange(32),rng.randrange(32)) for _ in range(8)]:
            tape={0:s}
            for side,x in [(-1,L),(1,R)]:
                for bit in range(x.bit_length()):tape[side*(bit+1)]=(x>>bit)&1
            tape[0]=w;head=-1 if D=='L' else 1
            sn=tape.get(head,0)
            Ln=sum(tape.get(head-i-1,0)<<i for i in range(max(L.bit_length(),R.bit_length())+2))
            Rn=sum(tape.get(head+i+1,0)<<i for i in range(max(L.bit_length(),R.bit_length())+2))
            X,Yv=(L,R) if D=='L' else (R,L);quotient,remainder=divmod(X,2)
            assert (sn,Ln,Rn)==((remainder,quotient,2*Yv+w) if D=='L' else (remainder,2*Yv+w,quotient))
            d=[v[0] for v in canonical(q,s,const(L),const(R))];phys=list(d);time=0;trace=[]
            for _ in range(6+3*quotient+remainder+3*Yv):
                status,i,t=event(d,M,H);assert status=='fire'
                wait=min(phys);assert [j for j,x in enumerate(phys) if x==wait]==[i]
                time+=wait;assert time==t;trace.append(i)
                d=[v+M[j][i] for j,v in enumerate(d)]
                phys=[v-wait+M[j][i] for j,v in enumerate(phys)]
                assert all(v>0 for v in phys) and d==[time+v for v in phys]
                counts['independent_concrete_events']+=1
            wanted=[i for word,K in blocks(q,s,remainder,rule) for _ in range(val(K,quotient,Yv)) for i in word]
            assert trace==wanted
            shift=2*len(trace)+7
            assert d==[v[0]+shift for v in canonical(qn,sn,const(Ln),const(Rn))]
            assert event(d,M,H)[1:]==(INDEX[f'{qn}:{sn}'],shift+1)
            counts['independent_macro_fixtures']+=1
    for L,R in [(0,0),(7,11),(10**300,10**500)]:
        a=[v[0] for v in canonical(9,1,const(L),const(R))]
        assert run(a,M,H,0)[:3]==('halt',[0]*46,1)
        counts['immediate_canonical_halts']+=1
    # Any canonical integer input has metadata strictly above every actual entry.
    for L,R in [(0,0),(6,0),(10**300,10**200)]:
        a=[v[0] for v in canonical(0,0,const(L),const(R))]
        assert a[0]+a[-1]+43==2*(L+R)+47>max(max(a),46,12)
        counts['loader_bound_cases']+=1

    # General common-column theorem beyond the residue-separated examples:
    # independently enumerate relative progression collisions, then simulate
    # the actual cross-increment matrix with both early and terminal ties.
    for case in range(3000):
        n=1+case%4;a=[rng.randrange(1,24) for _ in range(n+1)]
        b=[rng.randrange(6) for _ in range(n)];ds=[rng.randrange(1,9) for _ in range(n)]
        matrix=[[b[i]+(ds[i] if j==i else 0) for i in range(n)]+[0] for j in range(n+1)]
        streams=[set(range(a[i],a[-1]+1,ds[i])) for i in range(n)]
        obstruction=any(a[-1] in x for x in streams) or any(x&y for i,x in enumerate(streams) for y in streams[i+1:])
        status,actual,t,trace=run(a,matrix,n,1000)
        assert status==('tie' if obstruction else 'halt')
        if not obstruction:
            predicted=[max(0,-((a[i]-a[-1])//ds[i])) for i in range(n)]
            assert actual==predicted+[0] and t==a[-1]+sum(x*y for x,y in zip(b,predicted))
            counts['common_column_true_halts']+=1
        else:counts['common_column_ties']+=1
        counts['general_common_column_instances']+=1
    for x,height,k in product(range(7),range(7),range(1,6)):
        z=-((x-height-1)//k);p,s=max(z,0),max(-z,0);r=x+k*z-height-1;u=k-1-r
        assert min(p,s,r,u)>=0 and (x+k*(p-s)-height-1-r)**2+(r+u-k+1)**2+p*s==0
        found=[]
        for pp,ss,rr in product(range(9),range(9),range(k)):
            uu=k-1-rr
            if (x+k*(pp-ss)-height-1-rr)**2+pp*ss==0:found.append((pp,ss,rr,uu))
            counts['common_local_natural_assignments']+=1
        assert found==[(p,s,r,u)]
        counts['common_unique_fibres']+=1
    # Positive self-reset alone is insufficient for progression arguments.
    for diagonal in [0,-1]:
        status,p,t,trace=run([1,3,20],[[2+diagonal,0,0],[2,4,0],[2,0,0]],2,200)
        assert status=='cutoff' and p==[200,0,0]
        counts['nonpositive_relative_diagonal_locks']+=1
    assert run([1,3,20],[[2,0,0],[0,4,0],[0,0,0]],2,100)[:3]==('tie',[1,0,0],3)
    counts['earlier_tie_regression']+=1
    return {'status':'PASS','source_pins':PINS,'original_member_inventory':inventory,'counts':dict(counts),
            'scope':'Independent complete matrix and all-value affine proof; finite event/tape and common-column checks. Grouped polynomial/API proof assigned separately. No full universal fixed-arity equation or external-program loader cost claimed.'}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('root');p.add_argument('--output');a=p.parse_args()
    result=verify(a.root);raw=json.dumps(result,indent=2)+'\n'
    if a.output:Path(a.output).write_text(raw)
    print(raw,end='')
