"""Independent finite audit of a pruned T4 alphabet, using only literal TM data.

This is a mathematical candidate with a separately supplied completeness proof.
No final giant coefficient is expanded and no K215 accepting run is asserted.
"""
from collections import Counter
from pathlib import Path
import hashlib, itertools, json

HERE = Path(__file__).resolve().parent
TM_SHA = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
L,Q,R,V,H = 434,435,436,437,438
PHASE = {L,Q,R}
PAIRS = {(L,L),(L,Q),(Q,R),(R,R)}

def require(p, msg):
    if not p: raise ValueError(msg)

def parse_tm():
    raw = (HERE/'k215.tm').read_bytes()
    require(hashlib.sha256(raw).hexdigest() == TM_SHA, 'Wrong literal K215 table')
    lines = raw.decode('ascii').splitlines()
    require(lines[0] == '#! start 0', 'Wrong initial state')
    tr = {}
    for row in lines[1:]:
        q,b,w,d,n = row.split()
        q,b,w,n = map(int,(q,b,w,n))
        require((q,b) not in tr, 'Duplicate input')
        require(d in ('L','R'), 'Bad movement')
        tr[q,b] = (w,1 if d=='R' else -1,n)
    require(set(tr) == {(q,b) for q in range(215) for b in (0,1)}, 'Wrong domain')
    require(tr[0,0] == (1,1,93), 'Wrong initial action')
    tr.update({(215,b):(b,0,215) for b in (0,1)})
    return tr

def decode(x):
    if x<434:
        k,b = divmod(x,2)
        return b,None if k==0 else k-1
    if x in PHASE: return 0,0 if x==Q else None
    return None,None

D = [decode(x) for x in range(439)]
HEADLESS = [x for x in range(439) if D[x][1] is None]
HEADED = [x for x in range(439) if D[x][1] is not None]

def base_valid(w,tr):
    l,c,r,n = w
    if sum(D[x][1] is not None for x in (l,c,r))>1: return False
    if (c==V)!=(n==V) or (c==V and r==V) or (c==H and n==H): return False
    if c!=V and r!=V and (c==H)!=(r==H): return False
    if c==V: return True
    if c==H: return n in PHASE
    bit,state = D[c]
    if c in PHASE:
        if l==V and c!=L or r==V and c!=R: return False
        if r!=V and (c,r) not in PAIRS: return False
    if state is not None:
        move=tr[state,bit][1]
        if move==-1 and l==V or move==1 and r==V: return False
    if n==H: return state is None or state==215
    if n in PHASE or l==H or r==H: return False
    written = bit if state is None else tr[state,bit][0]
    incoming=[]
    for x,move in ((l,1),(c,0),(r,-1)):
        b,q = D[x]
        if q is not None and tr[q,b][1]==move: incoming.append(tr[q,b][2])
    return len(incoming)<=1 and D[n]==(written,incoming[0] if incoming else None)

def edge_valid(a,b):
    """Allowed horizontal edge, including a blank cell at each vertical margin."""
    if a==V: return b in {0,L,H}
    if b==V: return a in {0,R,H}
    if a==H or b==H: return a==b==H
    if a in PHASE or b in PHASE: return (a,b) in PAIRS
    return True  # both ordinary symbols, including ordinary head symbols

def extra_valid(w):
    l,c,r,n=w
    if not edge_valid(l,c) or not edge_valid(c,r): return False
    if c<434 and l==V and D[r][1] is not None: return False
    if c<434 and r==V and D[l][1] is not None: return False
    if n==H and any(D[x][1] not in (None,215) for x in (l,c,r)): return False
    return True

def valid(w,tr): return base_valid(w,tr) and extra_valid(w)

def next_candidates(l,c,r,tr):
    if c==V: return [V]
    if c==H: return [L,Q,R]
    out=[H]
    if l==H or r==H: return out
    b,q=D[c]
    incoming=[]
    for x,move in ((l,1),(c,0),(r,-1)):
        bx,qx=D[x]
        if qx is not None and tr[qx,bx][1]==move: incoming.append(tr[qx,bx][2])
    if len(incoming)<=1:
        written=b if q is None else tr[q,b][0]
        out.append(written+2*(incoming[0]+1) if incoming else written)
    return out

def enumerate_all(tr):
    out=[];base_count=0;triples=0
    for c in range(439):
        pairs=list(itertools.product(HEADLESS,repeat=2))
        if D[c][1] is None:
            pairs += list(itertools.product(HEADED,HEADLESS))
            pairs += list(itertools.product(HEADLESS,HEADED))
        for l,r in pairs:
            triples+=1
            for n in next_candidates(l,c,r,tr):
                w=(l,c,r,n)
                if base_valid(w,tr):
                    base_count+=1
                    if extra_valid(w): out.append(w)
    require(triples==46980, 'Incomplete horizontal census')
    require(base_count==37075, 'Inherited T4 count differs')
    out.sort()
    start=(L,Q,R,1);forbidden=(V,H,V,Q)
    require(start in out and forbidden in out,'Required selectors absent')
    out.remove(start);out.remove(forbidden)
    return [start,forbidden]+out,triples,base_count

def power5(n):
    p,e=1,0
    while p<n: p*=5;e+=1
    return p,e

def geometry(k):
    a=439;ell=max(2,(k+1).bit_length())
    p=max(0,(k-2*ell-7*a-4+1)//2)
    jmax=4*a+4+p;m=2*ell+11*a+8+2*p
    nd=m+1-k-4*a-4;ds=k+12*a;M=k+15*a+nd
    em=27*M;hc=51*M+3*a+1;t1=hc+2*em+a+1
    gap=4*((2*em-2)//4+1)+2 # least integer >2em with residue2 mod4
    t2=t1+gap
    U=4*(m+3)*(18*(k+4*a+4)+6)+8
    bmin=max(ell*(jmax+1)+3,ell*(4*a+4)+U.bit_length()+1,4)
    b,be=power5(bmin);cl,ce=power5(t2+2*em+2)
    require(gap>2*em and gap%4==2,'Bad band gap')
    require(cl-gap>em and t2+em<cl,'Bad support separation')
    return dict(k=k,ell=ell,p=p,jmax=jmax,m=m,nd=nd,dummy_start=ds,M=M,
                Emax=em,Hc=hc,T1=t1,T2=t2,bmin=bmin,b=b,L=cl,
                b_exponent=be,L_exponent=ce,d=b*cl,d_exponent=be+ce)

def support_audit(windows,g):
    a=439;k=len(windows);coords=((1,0),(1,1),(1,2),(2,1))
    def e(rc,u):
        r,c=rc
        return k+3*a+(2-r)*3*a+(2-c)*a+u
    copies={e(rc,u) for rc in coords for u in range(a)}
    M=g['M'];anchors=(M,3*M,9*M,27*M);ds=g['dummy_start']
    support=set(range(k))|copies|set(range(ds,ds+g['nd']))|set(anchors)
    require(len(support)==g['m']+1,'Support collision')
    require(ds+g['nd']<M,'Dummy range reaches anchor')
    Hc=g['Hc'];t1=g['T1'];t2=g['T2'];cl=g['L'];em=g['Emax']
    extra=support|{ds+1}
    require(not ({(t1-x)%cl for x in extra}&{(t2-x)%cl for x in extra}), 'Rotated bands collide')
    require({(9*M-x)%cl for x in support}&{(27*M-x)%cl for x in support}=={0},'False anchor alignment')
    bare=(3*a,Hc+a,8*M,24*M)
    targets=[]
    for u in range(a):
        targets.append((e((1,1),u),{e((2,1),u)},set(),{e((1,1),u)}))
        for dst,src in (((1,0),(1,1)),((1,1),(1,2))):
            targets.append((Hc+e(dst,u),{e(src,u)},{e(dst,u)},set()))
    targets += [(9*M,{M},set(),{9*M}),(27*M,{3*M},set(),{27*M})]
    require(len({v[0] for v in targets})==3*a+2,'Target collision')
    for t,at0,at1,at2 in targets:
        require({t-v for v in bare if t-v in support}==at0,'Bare native mismatch')
        require(({t-Hc} if t-Hc in support else set())==at1,'Right transport mismatch')
        require(({t} if t in support else set())==at2,'Temporal transport mismatch')
        require(t<t1-em,'Clause reaches native target')
    for t,other in ((t1,t2),(t2,t1)):
        require(not ({t-v for v in bare}&support),'Bare shift reaches clause')
        require(all(other+x-t not in support for x in support),'Clause bands interfere')
    ell=g['ell'];A=1<<ell
    mu=A-2+(pow(A,g['jmax']+1)-A)//(A-1)
    census=Counter((j,s) for w in windows for j,s in enumerate(w))
    total=k+sum((census[j,u]+1)*pow(A,1+j*a+u) for j in range(4) for u in range(a))
    total+=sum((k+1)*pow(A,4*a+t) for t in range(1,5))
    mass=(len(support)+2)*(2*total+6)
    require(2*mu.bit_count()+3*a+2==g['m'],'Wrong high-mask population')
    require(4*mass+8 < 1<<g['b'] and 2*mu+4 < 1<<g['b'],'Carry bound fails')
    require(all(0<=t1-x and t2-x<cl for x in support),'Bad clause exponent')
    coeff={}
    for i,w in enumerate(windows):
        coeff[i]=(1+sum(pow(A,1+j*a+s,5) for j,s in enumerate(w))
                  +sum(pow(A,4*a+t,5) for t in range(1,5)))%5
    for j,rc in enumerate(coords):
        for u in range(a): coeff[e(rc,u)]=pow(A,1+j*a+u,5)
    for t,x in enumerate(anchors,1): coeff[x]=pow(A,4*a+t,5)
    dc=(sum(pow(2,x,5) for x in bare)
        +sum(v*(pow(2,t1-x,5)+pow(2,t2-x,5)) for x,v in coeff.items()))%5
    require((2*dc-pow(2,Hc,5))%5==3,'Five-adic unit differs')
    return dict(native_positions=len(support),target_checks=len(targets),
        all_rotation_support_checks=True,exact_convolution_support=True,
        mu_population=mu.bit_count(),mu_bit_length=mu.bit_length(),
        clause_mass_bit_length=total.bit_length(),carry_bound_bit_length=(4*mass+8).bit_length(),
        native_MF_population=g['m']+1,MC_population=g['d']-g['m']-1,
        modulo_five_unit=3,MC_mod4=2,MF_native_mod8=4)

def specification(g,sha):
    return dict(schema='proveit-k215-pruned-t4-5268-v1',
        binding='P4-5268-tightband-5pow17',
        source_pin='f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
        machine_sha256=TM_SHA,alphabet=439,tile_count=5268,
        tile_file='pruned_t4_windows.json',tile_sha256=sha,
        start=[L,Q,R,1],forbidden=[V,H,V,Q],
        ordering='Start first, forbidden second, then remaining valid quadruples lexicographically',
        predicate='pruned_t4_check.py: valid',geometry=g,
        definitions={
            'a':'439','k':'5268','ell':'13','A':'2^13','rho':'2^78125',
            'B':'rho^9765625 = 2^(5^17)',
            'slots':'(1,0),(1,1),(1,2),(2,1), in this order',
            'e(r,c,u)':'k+3*a+(2-r)*3*a+(2-c)*a+u',
            'E':'0..k-1; e(r,c,u) for slots and u=0..438; dummy_start..dummy_start+nd-1; M,3M,9M,27M',
            'mu':'A-2+sum(A^j,j=1..jmax)',
            'v_selector(i)':'1+sum(A^(1+j*a+w_i[j]),j=0..3)+sum(A^(4*a+t),t=1..4)',
            'v_copy(j,u)':'A^(1+j*a+u) at e(slots[j],u)',
            'v_anchor(t)':'A^(4*a+t) at 3^(t-1)*M,t=1..4',
            'v_dummy':'0',
            'DC':'rho^(3*a)+rho^(Hc+a)+rho^(8*M)+rho^(24*M)+sum(v_e*(rho^(T1-e)+rho^(T2-e)),e in E)',
            'DR':'rho^Hc',
            'MF0':'mu*(rho^T1+rho^T2)+sum(rho^e(1,1,u),u=0..438)+sum(rho^(Hc+e(r,c,u)),(r,c)=(1,0),(1,1),u=0..438)+rho^(9*M)+rho^(27*M)',
            'MC':'B-1-sum(rho^e,e in E except1)-2*rho^dummy_start',
            'MF_native':'MF0+4','beta':'B-1','K':'DC+B*DR','MF_source':'MF_native+B-1'},
        ports=['beta','K','MC','MF_source'],
        invariants={'MC_mod4':2,'MF_native_mod8':4,'population_sum':'5^17','mod5_unit':3},
        coefficient_binding_warning='Use this entire tuple, not a mixture of old coefficient recipes',
        final_coefficients_expanded=False)

def seam_checks(tr):
    results=[]
    for control in range(2):
        tm=dict(tr)
        tm[93,0]=(0,0,215) if control==0 else (1,-1,2)
        tm[2,1]=(0,-1,3);tm[3,0]=(1,1,215)
        tape={};head=state=0;history=[]
        for step in range(10):
            history.append((dict(tape),head,state))
            if state==215: break
            w,m,state=tm[state,tape.get(head,0)];tape[head]=w;head+=m
        require(history[-1][2]==215,'Control failed to halt')
        lo=min(h for _,h,_ in history);hi=max(h for _,h,_ in history)
        for extra_width,extra_height in itertools.product(range(4),repeat=2):
            xs=3-lo;width=hi+xs+4+extra_width;height=len(history)+1+extra_height
            word=[None]*(width*height)
            for y in range(height):
                for x in range(width):
                    if x==0: cell=V
                    elif y==0: cell=H
                    elif y==1: cell=L if x<xs else Q if x==xs else R
                    else:
                        tape,head,state=history[min(y-1,len(history)-1)];pos=x-xs
                        cell=tape.get(pos,0)+(2*(state+1) if pos==head else 0)
                    at=(-(x-xs)-width*(y-1))%len(word)
                    require(word[at] is None,'Nonbijective cyclic construction')
                    word[at]=cell
            ws=[(word[(i+1)%len(word)],word[i],word[(i-1)%len(word)],word[(i-width)%len(word)]) for i in range(len(word))]
            require(all(valid(w,tm) for w in ws),'Pruning rejected a canonical helix')
            require(ws[0]==(L,Q,R,1),'Start moved')
            require((V,H,V,Q) not in ws,'Forbidden tile appears')
            results.append(dict(control=control,width=width,height=height,windows=len(ws)))
    return results

def main():
    tr=parse_tm();windows,triples,old=enumerate_all(tr)
    require(len(windows)==5268,'Pruned alphabet count differs')
    counts=Counter(w[1] for w in windows)
    named={str(c):counts[c] for c in (0,1,432,433,L,Q,R,V,H)}
    work=Counter(counts[c] for c in range(2,432))
    expected={0:1754,1:1744,432:8,433:8,L:6,Q:1,R:6,V:9,H:12}
    require(all(counts[c]==n for c,n in expected.items()),'Closed center census differs')
    require(work=={4:430},'Working-center census differs')
    blob=(json.dumps(windows,separators=(',',':'))+'\n').encode()
    (HERE/'pruned_t4_windows.json').write_bytes(blob)
    g=geometry(len(windows));sha=hashlib.sha256(blob).hexdigest()
    result=dict(status='PASS',old_count=old,new_count=len(windows),triples=triples,
        centers=named,working_center_counts=dict(work),geometry=g,
        windows_sha256=sha,support_audit=support_audit(windows,g),seams=seam_checks(tr),
        scope='Exact finite predicate, count and padded-control checks; not an unbounded semantic proof')
    (HERE/'pruned_t4_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    (HERE/'pruned_t4_constants.json').write_text(json.dumps(specification(g,sha),indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
