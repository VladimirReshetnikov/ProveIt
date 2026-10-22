"""Exact finite compiler checks for a pruned K215 T4 local alphabet.

Independent generation reads only the literal transition table, never searches
for K215 halting and never expands the final astronomical coefficients.
"""
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

if not __debug__:
    raise SystemExit('Run without -O: this audit requires Python assertions.')

ROOT=Path(__file__).parent
TRANSITIONS=json.loads((ROOT/'k215_transitions.json').read_text())['transitions']
TM_BYTES=(ROOT/'k215.tm').read_bytes()
assert hashlib.sha256(TM_BYTES).hexdigest()=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
TM_ROWS=[]
for line in TM_BYTES.decode().splitlines():
    if not line.strip() or line.startswith('#'):continue
    q,b,w,move,nq=line.split()
    TM_ROWS.append([int(q),int(b),int(w),{'L':-1,'R':1}[move],int(nq)])
assert TM_ROWS==TRANSITIONS and len(TRANSITIONS)==430
DELTA={(q,b):(w,d,nq) for q,b,w,d,nq in TRANSITIONS}
DELTA.update({(215,b):(b,0,215) for b in (0,1)})
L,Q,R,V,H=434,435,436,437,438
PHASES={L,Q,R}
PHASE_EDGES={(L,L),(L,Q),(Q,R),(R,R)}
START=(L,Q,R,1)
FORBIDDEN=(H,0,0,H)

def data(x):
    if x<434:
        v,b=divmod(x,2)
        return b, None if v==0 else v-1, None
    if x in PHASES:
        return 0, 0 if x==Q else None, x
    return None,None,None

DATA=[data(x) for x in range(439)]
HEADLESS=[x for x in range(439) if DATA[x][1] is None]
HEADED=[x for x in range(439) if DATA[x][1] is not None]

def edge(x,y):
    """A globally necessary horizontal edge condition for padded tableaux."""
    if x==V or y==V:
        if x==y:return False
        if y in PHASES:return y==L
        if x in PHASES:return x==R
        return True
    if (x==H)!=(y==H):return False
    if x in PHASES or y in PHASES:return (x,y) in PHASE_EDGES
    return True

def triple_filter(l,c,r):
    if sum(DATA[x][1] is not None for x in (l,c,r))>1:return False
    if not(edge(l,c) and edge(c,r)):return False
    if V in(l,c,r):
        if any(DATA[x][1] is not None or x==1 for x in(l,c,r)):return False
    return True

def old_valid(w,transition=DELTA):
    """The T4 predicate, written explicitly for the subset inclusion audit."""
    l,c,r,n=w
    if sum(DATA[x][1] is not None for x in(l,c,r))>1:return False
    if (c==V)!=(n==V) or c==V and r==V or c==H and n==H:return False
    if c!=V and r!=V and (c==H)!=(r==H):return False
    if c==V:return True
    if c==H:return n in PHASES
    b,q,p=DATA[c]
    if p is not None:
        if l==V and p!=L or r==V and p!=R:return False
        if r!=V and (p,DATA[r][2]) not in PHASE_EDGES:return False
    if q is not None:
        _,move,_=transition[q,b]
        if move==-1 and l==V or move==1 and r==V:return False
    if n==H:return q is None or q==215
    if DATA[n][2] is not None or l==H or r==H:return False
    expected_b=b if q is None else transition[q,b][0]
    arrivals=[]
    for x,move in((l,1),(c,0),(r,-1)):
        bx,qx,_=DATA[x]
        if qx is not None and transition[qx,bx][1]==move:
            arrivals.append(transition[qx,bx][2])
    return len(arrivals)<=1 and DATA[n][:2]==(expected_b,arrivals[0] if arrivals else None)

def valid(w,transition=DELTA):
    if w==FORBIDDEN:return old_valid(w,transition)
    l,c,r,n=w
    if not triple_filter(l,c,r):return False
    if n==H and any(x in PHASES or (DATA[x][1] is not None and DATA[x][1]!=215) for x in(l,c,r)):
        return False
    if c==H and ((l==V and n!=L) or (r==V and n!=R)):
        return False
    return old_valid(w,transition)

def generate():
    triples=set(itertools.product(HEADLESS,repeat=3))
    for pos in range(3):
        for hd in HEADED:
            for a,b in itertools.product(HEADLESS,repeat=2):
                triple=[a,b];triple.insert(pos,hd);triples.add(tuple(triple))
    passing=[t for t in sorted(triples) if triple_filter(*t)]
    out=[t+(n,) for t in passing for n in range(439) if valid(t+(n,))]
    assert START in out and FORBIDDEN not in out
    out.remove(START)
    windows=[START,FORBIDDEN]+out
    assert len(windows)==5252 and len(set(windows))==5252
    assert all(old_valid(w) for w in windows)
    groups=Counter('bits' if w[1]<2 else 'working_head' if w[1]<432 else 'halt_head' if w[1]<434 else {L:'L',Q:'Q',R:'R',V:'V',H:'H'}[w[1]] for w in windows)
    assert groups==dict(bits=3495,working_head=1720,halt_head=16,L=3,Q=1,R=3,V=9,H=5)
    return windows,dict(unfiltered_horizontal_triples=len(triples),filtered_horizontal_triples=len(passing),candidate_quadruples=len(passing)*439,groups=dict(groups))

def geometry(windows,compact=False):
    k=len(windows);a=439;ell=(k+1).bit_length()
    base=2*ell+11*a+8
    p=max(0,(k+4*a+4-base+1)//2);m=base+2*p
    nd=m+1-k-4*a-4;es=k+12*a;M=k+15*a+nd
    multipliers=(1,2,3,7) if compact else (1,3,9,27)
    shifts=(2*M,5*M) if compact else (8*M,24*M)
    tested=(3*M,7*M) if compact else (9*M,27*M)
    sourced=(M,2*M) if compact else (M,3*M)
    emax=max(multipliers)*M
    Hc=51*M+3*a+1
    t1=Hc+2*emax+a+1;t2=t1+2*emax+4
    assert emax%2==1
    coordinates=((1,0),(1,1),(1,2),(2,1))
    def e(rc,s):
        r,c=rc;return k+3*a+(2-r)*3*a+(2-c)*a+s
    copies={e(rc,s) for rc in coordinates for s in range(a)}
    anchors={x*M for x in multipliers}
    support=set(range(k))|copies|set(range(es,es+nd))|anchors
    assert len(support)==m+1
    Lcell=1
    while Lcell<t2+2*emax+2:Lcell*=5
    bmin=max(ell*(4*a+5+p)+3,ell*(4*a+4)+(4*(m+3)*(18*(k+4*a+4)+6)+8).bit_length()+1,4)
    b=1
    while b<bmin:b*=5
    expand=support|{es+1}
    assert not ({(t1-x)%Lcell for x in expand}&{(t2-x)%Lcell for x in expand})
    assert {(tested[0]-x)%Lcell for x in support}&{(tested[1]-x)%Lcell for x in support}=={0}
    bare=(3*a,Hc+a,*shifts)
    target=[]
    for s in range(a):
        target.append((e((1,1),s),{e((2,1),s)},set(),{e((1,1),s)}))
        for rc,src in(((1,0),(1,1)),((1,1),(1,2))):
            target.append((Hc+e(rc,s),{e(src,s)},{e(rc,s)},set()))
    target += [(tested[j],{sourced[j]},set(),{tested[j]}) for j in range(2)]
    assert len({t for t,*_ in target})==3*a+2
    for t,at0,at1,at2 in target:
        assert {t-v for v in bare if t-v in support}==at0,(t,at0)
        assert ({t-Hc} if t-Hc in support else set())==at1
        assert ({t} if t in support else set())==at2
        assert t<t1-emax
    for t,other in((t1,t2),(t2,t1)):
        assert not {t-v for v in bare}&support
        assert all(other+x-t not in support for x in support)
    A5=pow(2,ell,5);coeff={}
    for i,w in enumerate(windows):
        coeff[i]=(1+sum(pow(A5,1+j*a+s,5) for j,s in enumerate(w))+sum(pow(A5,4*a+t,5) for t in range(1,5)))%5
    for j,rc in enumerate(coordinates):
        for s in range(a):coeff[e(rc,s)]=pow(A5,1+j*a+s,5)
    for j,x in enumerate(sorted(anchors),1):coeff[x]=pow(A5,4*a+j,5)
    dc=(sum(pow(2,x,5) for x in bare)+sum(v*(pow(2,t1-x,5)+pow(2,t2-x,5)) for x,v in coeff.items()))%5
    unit=(2*dc-pow(2,Hc,5))%5
    assert unit!=0
    A=1<<ell;jmax=4*a+4+p
    mu=A-2+(pow(A,jmax+1)-A)//(A-1)
    census=Counter((j,s) for w in windows for j,s in enumerate(w))
    sum_v=k+sum((census[j,s]+1)*pow(A,1+j*a+s) for j in range(4) for s in range(a))+sum((k+1)*pow(A,4*a+t) for t in range(1,5))
    mass=(len(support)+2)*(2*sum_v+6)
    assert 2*mu.bit_count()+3*a+2==m
    assert 4*mass+8 < (1<<b) and 2*mu+4 < (1<<b)
    assert t2+2*emax+2<=Lcell and t2-t1>2*emax and (t2-t1)%4==2
    return dict(k=k,ell=ell,p=p,m=m,dummy_count=nd,dummy_start=es,M=M,Emax=emax,Hc=Hc,T1=t1,T2=t2,bmin=bmin,b=b,L=Lcell,d=b*Lcell,native_support=len(support),target_positions=len(target),mod5_unit=unit,copy_offsets={name:e(rc,0) for name,rc in zip(('left','center','right','next'),coordinates)},anchors=sorted(anchors),anchor_shifts=list(shifts),anchor_targets=list(tested),mu_top_power=jmax,mu_population=mu.bit_count(),mu_bit_length=mu.bit_length(),clause_mass_bit_length=sum_v.bit_length(),carry_threshold_bit_length=(4*mass+8).bit_length(),beta_bit_length=b*Lcell,K_bit_length=b*(Lcell+Hc)+1,all_rotation_checks=True,convolution_target_checks=True)

def seam_checks():
    checked=0;tableaux=0
    for control in (0,1):
        tr=dict(DELTA)
        tr[93,0]=(0,0,215) if control==0 else (1,-1,2)
        tr[2,1]=(0,-1,3);tr[3,0]=(1,1,215)
        tape={};head=state=0;history=[]
        for _ in range(10):
            history.append((dict(tape),head,state))
            if state==215:break
            write,move,state=tr[state,tape.get(head,0)];tape[head]=write;head+=move
        assert history[-1][2]==215
        lm=max(3,3-min(h for _,h,_ in history));rm=max(3,3+max(h for _,h,_ in history))
        for dw,dh in itertools.product(range(3),repeat=2):
            width=lm+rm+2+dw;height=len(history)+1+dh;xs=lm+1
            grid=[]
            for y in range(height):
                row=[V]
                for x in range(1,width):
                    if y==0:cell=H
                    elif y==1:cell=L if x<xs else Q if x==xs else R
                    else:
                        tape,head,state=history[min(y-1,len(history)-1)];pos=x-xs
                        cell=tape.get(pos,0)+(2*(state+1) if pos==head else 0)
                    row.append(cell)
                grid.append(row)
            word=[None]*(width*height)
            for y,row in enumerate(grid):
                for x,v in enumerate(row):word[(-(x-xs)-width*(y-1))%len(word)]=v
            windows=[(word[(i+1)%len(word)],word[i],word[(i-1)%len(word)],word[(i-width)%len(word)]) for i in range(len(word))]
            assert all(valid(w,tr) for w in windows),[w for w in windows if not valid(w,tr)]
            assert windows[0]==START and windows.count(START)==1
            assert FORBIDDEN not in windows
            checked+=len(windows);tableaux+=1
    return dict(control_tableaux=tableaux,windows_checked=checked)

if __name__=='__main__':
    windows,census=generate()
    dest=ROOT/'pruned_t4_windows.json'
    dest.write_text(json.dumps(windows,separators=(',',':'))+'\n')
    result=dict(status='PASS',tile_count=len(windows),sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),machine_table_sha256=hashlib.sha256(TM_BYTES).hexdigest(),transition_projection_sha256=hashlib.sha256((ROOT/'k215_transitions.json').read_bytes()).hexdigest(),literal_table_projection_match=True,census=census,retained_geometry=geometry(windows),compact_geometry=geometry(windows,True),seams=seam_checks(),scope='Exact finite alphabet, geometry, carry and toy seam checks; not an end-to-end formal proof or test of K215 halting.')
    (ROOT/'pruned_t4_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
