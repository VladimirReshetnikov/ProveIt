"""Finite verifier for a stricter, densely packed K215 T4 compiler.

This checks finite local data and coefficient geometry. It does not decide
K215 halting or prove the universal Diophantine compiler theorem.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,itertools
import check_t4 as old
from explore_t4 import strict,enumeration,kind

ROOT=Path(__file__).parent

def verify_machine():
    raw=(ROOT/'sources/k215_transitions.json').read_bytes()
    tm=(ROOT/'sources/k215.tm').read_bytes()
    expected_json='880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755'
    expected_tm='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
    expected_semantic='c6075157c74077e27fbcea05b35ab8b3a6ef0a976c08f442653f809eb1fe2d61'
    assert hashlib.sha256(raw).hexdigest()==expected_json
    assert hashlib.sha256(tm).hexdigest()==expected_tm
    obj=json.loads(raw);rows=obj['transitions']
    assert hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest()==expected_semantic
    parsed=[]
    for line in tm.decode('ascii').splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,nq=line.split()
        parsed.append([int(q),int(b),int(w),{'L':-1,'R':1}[d],int(nq)])
    assert parsed==rows
    assert {(q,b) for q,b,w,d,nq in rows}==set(itertools.product(range(215),range(2)))
    assert all(w in (0,1) and d in (-1,1) and 0<=nq<=215 for q,b,w,d,nq in rows)
    assert rows[0]==[0,0,1,1,93]
    assert [row for row in rows if row[-1]==215]==[[68,1,1,1,215]]
    return dict(tm_sha256=expected_tm,json_sha256=expected_json,
      transitions_semantic_sha256=expected_semantic,literal_tm_matches_transition_rows=True,
      states=215,transitions=430,initial_state=0,halt_state=215,blank_symbol=0)

def reduced_windows():
    ws=enumeration(3)
    start=(old.L,old.Q,old.R,1)
    forbidden=(old.H,0,0,old.H)
    assert start in ws and forbidden not in ws
    ws.remove(start)
    return [start,forbidden]+ws

def geometry(windows):
    a=439;k=len(windows);ell=(k+1).bit_length()
    # Original population balance retained exactly.
    base=2*ell+11*a+8
    padding=max(0,(k+4*a+4-base+1)//2)
    m=base+2*padding
    nd=m+1-k-4*a-4
    dummy_start=k+5*a
    M=4*((dummy_start+nd+2+3)//4)
    Emax=6*M
    Hc=9*M+3*a+1
    T1=Hc+2*Emax+a+1
    gap=2*Emax+(2 if Emax%2==0 else 4)
    T2=T1+gap
    Lcell=1
    while Lcell<T2+2*Emax+2:Lcell*=5
    bmin=max(ell*(4*a+5+padding)+3,
      ell*(4*a+4)+(4*(m+3)*(18*(k+4*a+4)+6)+8).bit_length()+1,4)
    b=1
    while b<bmin:b*=5
    offsets=[k+4*a,k+3*a,k+2*a,k]
    copies={offset+u for offset in offsets for u in range(a)}
    anchor_list=[M,3*M,2*M,6*M]
    anchors=set(anchor_list)
    support=set(range(k))|copies|set(range(dummy_start,dummy_start+nd))|anchors
    assert len(support)==m+1
    assert max(support-anchors)<M and len(anchors)==4
    expanded=support|{dummy_start+1}
    assert not ({(T1-e)%Lcell for e in expanded}&{(T2-e)%Lcell for e in expanded})
    assert {(2*M-e)%Lcell for e in support}&{(6*M-e)%Lcell for e in support}=={0}
    bare=(3*a,Hc+a,M,3*M)
    targets=[]
    for u in range(a):
        # Current next = temporal-neighbor center.
        targets.append((offsets[1]+u,{offsets[3]+u},set(),{offsets[1]+u}))
        # Current center = right-neighbor left; current right = right-neighbor center.
        targets.append((Hc+offsets[0]+u,{offsets[1]+u},{offsets[0]+u},set()))
        targets.append((Hc+offsets[1]+u,{offsets[2]+u},{offsets[1]+u},set()))
    targets.extend([(2*M,{M},set(),{2*M}),(6*M,{3*M},set(),{6*M})])
    assert len({t for t,*_ in targets})==3*a+2
    for t,at0,at1,at2 in targets:
        assert {t-v for v in bare if t-v in support}==at0,(t,'DC')
        assert ({t-Hc} if t-Hc in support else set())==at1,(t,'DR')
        assert ({t} if t in support else set())==at2,(t,'rotation')
        assert t<T1-Emax
    for t,other in [(T1,T2),(T2,T1)]:
        assert not {t-v for v in bare}&support
        assert all(other+x-t not in support for x in support)
    A=1<<ell
    mu=A-2+(pow(A,4*a+5+padding)-A)//(A-1)
    census=Counter((j,u) for w in windows for j,u in enumerate(w))
    sum_v=k+sum((census[j,u]+1)*pow(A,1+j*a+u) for j in range(4) for u in range(a))+sum((k+1)*pow(A,4*a+t) for t in range(1,5))
    mass=(len(support)+2)*(2*sum_v+6)
    assert 2*mu.bit_count()+3*a+2==m
    assert 4*mass+8<(1<<b) and 2*mu+4<(1<<b)
    assert T2+2*Emax+2<=Lcell and gap>2*Emax and gap%4==2
    assert 2*Emax<Lcell
    # Full literal coefficient residue, independent of the two-band simplification.
    coeff={i:(1+sum(pow(A,1+j*a+u,5) for j,u in enumerate(w))+sum(pow(A,4*a+t,5) for t in range(1,5)))%5 for i,w in enumerate(windows)}
    for j,offset in enumerate(offsets):
        for u in range(a):coeff[offset+u]=pow(A,1+j*a+u,5)
    for t,e in enumerate(anchor_list,1):coeff[e]=pow(A,4*a+t,5)
    dc=(sum(pow(2,b*x,5) for x in bare)+sum(v*(pow(2,b*(T1-e),5)+pow(2,b*(T2-e),5)) for e,v in coeff.items()))%5
    unit=(2*dc-pow(2,b*Hc,5))%5
    assert unit==3
    return dict(alphabet=a,tiles=k,ell=ell,A=A,padding=padding,mu_top=4*a+4+padding,
      mu_population=mu.bit_count(),mu_bit_length=mu.bit_length(),
      m=m,native_positions=len(support),dummy_count=nd,dummy_start=dummy_start,
      copy_offsets=dict(zip(['left','center','right','next'],offsets)),
      anchor_order=anchor_list,M=M,Emax=Emax,Hc=Hc,T1=T1,T2=T2,
      bmin=bmin,b=b,L=Lcell,d=b*Lcell,beta_bit_length=b*Lcell,
      K_bit_length=b*(Lcell+Hc)+1,
      bare_shifts=list(bare),carry_threshold_bit_length=(4*mass+8).bit_length(),
      mod5_unit=unit,convolution_targets=len(targets),
      all_rotation_band_and_anchor_checks=True)

def seam_checks():
    checked=0
    for control in(0,1):
        tr=dict(old.delta)
        tr[93,0]=(0,0,215) if control==0 else (1,-1,2)
        tr[2,1]=(0,-1,3);tr[3,0]=(1,1,215)
        tape={};head=state=0;history=[]
        for _ in range(10):
            history.append((dict(tape),head,state))
            if state==215:break
            write,move,state=tr[state,tape.get(head,0)]
            tape[head]=write;head+=move
        assert history[-1][2]==215
        lm=max(3,3-min(h for _,h,_ in history));rm=max(3,3+max(h for _,h,_ in history))
        for dw,dh in itertools.product(range(3),repeat=2):
            width=lm+rm+2+dw;height=len(history)+1+dh;xs=lm+1
            grid=[]
            for y in range(height):
                row=[old.V]
                for x in range(1,width):
                    if y==0:cell=old.H
                    elif y==1:cell=old.L if x<xs else old.Q if x==xs else old.R
                    else:
                        tp,hd,st=history[min(y-1,len(history)-1)];pos=x-xs
                        cell=tp.get(pos,0)+(2*(st+1) if pos==hd else 0)
                    row.append(cell)
                grid.append(row)
            word=[None]*(width*height)
            for y,row in enumerate(grid):
                for x,v in enumerate(row):word[(-(x-xs)-width*(y-1))%len(word)]=v
            ws=[(word[(i+1)%len(word)],word[i],word[(i-1)%len(word)],word[(i-width)%len(word)]) for i in range(len(word))]
            for w in ws:
                l,c,r,n=w
                from explore_t4 import adj
                assert adj(l,c) and adj(c,r)
                assert old.V not in (l,c,r) or not any(kind(x)=='o' and x!=0 for x in (l,c,r))
                assert n!=old.H or all(old.D[x][1] in (None,215) for x in (l,c,r))
                assert old.valid(w,tr)
            assert ws[0]==(old.L,old.Q,old.R,1) and ws.count((old.L,old.Q,old.R,1))==1
            checked+=len(ws)
    return checked

def coefficient_specification(receipt):
    return dict(schema='proveit-k215-strict-dense-t4-fixed-coefficients-v1',
      status='Explicit finite recipe with mathematical adapter and finite checks; not end-to-end kernel formalized',
      repository='VladimirReshetnikov/ProveIt',
      repository_commit='f0ae4e0991ca44a7bb4e5671d42e33d775e48035',
      baseline_package='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/11-t4',
      machine=receipt['machine'],
      free_parameters=[],coefficient_ports=['beta','K','M_C','M_F_src'],
      scalars=receipt['geometry'],
      tiles=dict(count=5280,file='reduced_t4_windows.json',
        sha256=receipt['windows_sha256'],
        start=[434,435,436,1],forbidden=[438,0,0,438],
        order='Start first, Forbidden second, then every other strict tile lexicographically',
        predicate='explore_t4.strict(w,3), with old check_t4.valid; Forbidden is separately included',
        ordinary_head_code='2*(q+1)+b, q=0,...,215, b=0,1',
        ordinary_headless_codes=[0,1],L=434,Q=435,R=436,V=437,H=438),
      definitions={
        'A':'8192 = 2^13',
        'rho':'2^78125',
        'B':'rho^390625 = 2^(5^15)',
        'E':'{0,...,5279} union {7036+u,6597+u,6158+u,5280+u : u=0,...,438} union {7475,7476,7480,22440,14960,44880}',
        'e_left(u)':'7036+u',
        'e_center(u)':'6597+u',
        'e_right(u)':'6158+u',
        'e_next(u)':'5280+u',
        'mu':'A-2+sum(A^j,j=1,...,2849)',
        'v_selector(i)':'1+A^(1+w_i.left)+A^(440+w_i.center)+A^(879+w_i.right)+A^(1318+w_i.next)+sum(A^(1756+t),t=1,...,4)',
        'v_left_copy(u)':'A^(1+u)',
        'v_center_copy(u)':'A^(440+u)',
        'v_right_copy(u)':'A^(879+u)',
        'v_next_copy(u)':'A^(1318+u)',
        'v_anchor(t)':'A^(1756+t) at e=(7480,22440,14960,44880)[t-1], t=1,...,4',
        'v_dummy':'0 at positions7475 and7476',
        'D_C':'rho^1317+rho^69077+rho^7480+rho^22440+sum(v_e*(rho^(158838-e)+rho^(248600-e)),e in E)',
        'D_R':'rho^68638',
        'M_F0':'mu*(rho^158838+rho^248600)+sum(rho^(6597+u),u=0,...,438)+sum(rho^(68638+7036+u)+rho^(68638+6597+u),u=0,...,438)+rho^14960+rho^44880',
        'M_C':'B-1-sum(rho^e,e in E except1)-2*rho^7475',
        'M_F_nat':'M_F0+4',
        'beta':'B-1',
        'K':'D_C+B*D_R',
        'M_F_src':'M_F_nat+B-1'},
      compiler_invariants=dict(M_C_mod4=2,M_F_nat_mod8=4,
        M_C_population='d-7042',M_F_nat_population=7042,population_sum='d=5^15',
        mod5_unit_2D_C_minus_D_R=3),
      source_files=dict(tm='sources/k215.tm',transitions='sources/k215_transitions.json'),
      verification=dict(checker='check_reduced.py',receipt='reduced_t4_receipt.json',
        mathematical_proof='REDUCED_T4_PROOF.md'),
      warning='Use the complete four-tuple. The four enormous integers are fully specified but not expanded.')

if __name__=='__main__':
    machine=verify_machine()
    windows=reduced_windows();assert len(windows)==5280
    dest=ROOT/'reduced_t4_windows.json'
    dest.write_text(json.dumps(windows,separators=(',',':'))+'\n')
    counts=Counter(w[1] for w in windows)
    # Independent class census: interior headless centers have
    # 4+2*432*2 ordinary successors and4+2*2*2 closing-H successors.
    headless_interior=4+2*432*2+4+2*2*2
    assert counts[0]==headless_interior+6+1 # six wall cases plus Forbidden
    assert counts[1]==headless_interior
    assert all(counts[x]==4 for x in range(2,432))
    assert counts[432]==counts[433]==8
    assert [counts[x] for x in (old.L,old.Q,old.R,old.V,old.H)]==[6,1,6,24,12]
    receipt=dict(status='PASS',machine=machine,window_count=len(windows),
        exhaustive_domain=enumeration.stats,
        windows_sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),
        center_class_counts={
          'headless_ordinary':sum(counts[x] for x in (0,1)),
          'working_heads':sum(counts[x] for x in range(2,432)),
          'halt_heads':sum(counts[x] for x in (432,433)),
          'L':counts[old.L],'Q':counts[old.Q],'R':counts[old.R],
          'V':counts[old.V],'H':counts[old.H]},
        geometry=geometry(windows),seam_windows=seam_checks(),
        scope='Finite literal alphabet, coefficient support and control-machine seam checks only.')
    (ROOT/'reduced_t4_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (ROOT/'COEFFICIENTS.json').write_text(json.dumps(coefficient_specification(receipt),indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
