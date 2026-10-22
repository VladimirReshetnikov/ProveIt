import sys
if sys.flags.optimize:
    raise SystemExit("Do not run these evidence checks with -O or PYTHONOPTIMIZE.")
#!/usr/bin/env python3
"""New, independent audit and closed coefficient description.

Received repository scripts are read as source only, never imported/executed.
Run after the independently authored C++ exhaustive center/pair enumeration.
"""
from pathlib import Path
from itertools import product
from hashlib import sha256
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
MACHINE=ROOT/'diophantine_zfc_compiler/k215.tm'
DATA=ROOT/'diophantine_zfc_round2/review/06-blank67/data'
ROWS=[]
for line in MACHINE.read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split()
        ROWS.append(tuple(map(int,(q,b,w)))+(1 if d=='R' else -1,int(t)))
TABLE={(q,b):(w,d,t) for q,b,w,d,t in ROWS}
TABLE.update({(215,b):(b,0,215) for b in (0,1)})
A=439
LEFT,START,RIGHT,VERT,HORIZ=range(434,439)
S=(438,438,438,434,435,436,0,1,188)
BAD=(0,438,0,0,437,438,0,437,0)

def content(code):
    if code<434:return code%2,code//2-1
    if code in (LEFT,RIGHT,VERT):return 0,-1
    if code==START:return 0,0
    return None

def has_head(code):
    p=content(code)
    return p is not None and p[1]>=0

def allowed(window,table=TABLE,prune=True):
    if len(window)!=9 or any(type(c) is not int or not 0<=c<A for c in window):return False
    if prune and any(sum(map(has_head,window[3*r:3*r+3]))>1 for r in range(3)):return False
    prior,left,center,right,nxt=(window[i] for i in (1,3,4,5,7))
    if (center==VERT)!=(nxt==VERT):return False
    if center==VERT and right==VERT:return False
    if center==HORIZ and nxt==HORIZ:return False
    if center!=VERT and right!=VERT and (center==HORIZ)!=(right==HORIZ):return False
    if center in (VERT,HORIZ):return True
    phase=center in (LEFT,START,RIGHT)
    if phase!=(prior==HORIZ):return False
    if phase:
        if left==VERT and center!=LEFT:return False
        if right==VERT and center!=RIGHT:return False
        if right!=VERT and (center,right) not in {(LEFT,LEFT),(LEFT,START),(START,RIGHT),(RIGHT,RIGHT)}:return False
    bit,state=content(center)
    if state>=0:
        written,movement,_=table[state,bit]
        if nxt==HORIZ and state!=215:return False
        if movement==-1 and left==VERT or movement==1 and right==VERT:return False
    else:written=bit
    if nxt==HORIZ:return True
    if left==HORIZ or right==HORIZ:return False
    incoming=[]
    for code,move in ((left,1),(center,0),(right,-1)):
        b,q=content(code)
        if q>=0 and table[q,b][1]==move:incoming.append(table[q,b][2])
    return len(incoming)<=1 and content(nxt)==(written,incoming[0] if incoming else -1)

def row_limited_formula():
    """Closed count, independent of the C++ local-predicate implementation."""
    left_in=sum(d==1 for q,b,w,d,t in ROWS)+1
    right_in=sum(d==-1 for q,b,w,d,t in ROWS)
    target0_left=sum(d==1 and t==0 for q,b,w,d,t in ROWS)
    target0_right=sum(d==-1 and t==0 for q,b,w,d,t in ROWS)
    assert (left_in,right_in,target0_left,target0_right)==(349,82,4,0)
    # Six headless codes, 433 headed codes. For a fixed row center:
    # headed: 6^2 choices of corners; headless: 6^2+2*6*433 choices.
    headed_corner=36
    blank_corner=5232
    all_prior=433*headed_corner+6*blank_corner
    ordinary_prior=all_prior-blank_corner
    no_arrival=25+5*(433-left_in)+5*(433-right_in)
    one_arrival=5*(left_in+right_in)
    zero_arrival=5*(target0_left+target0_right)
    boundary_pairs=6*5+433*5+6*433
    counts={}
    counts[VERT]=all_prior*boundary_pairs*blank_corner
    counts[HORIZ]=all_prior*(2*439)*(433*headed_corner+4*blank_corner)
    counts[0]=ordinary_prior*(boundary_pairs*blank_corner+no_arrival*3*blank_corner+(one_arrival+zero_arrival)*headed_corner)
    counts[1]=ordinary_prior*(boundary_pairs*blank_corner+no_arrival*blank_corner+one_arrival*headed_corner)
    for b in (0,1):counts[432+b]=ordinary_prior*(30*blank_corner+25*headed_corner)
    for q,b,w,d,t in ROWS:counts[2*(q+1)+b]=ordinary_prior*20*blank_corner*(3 if w==0 else 1)
    counts[LEFT]=blank_corner*(445*blank_corner+94*3*blank_corner+353*headed_corner)
    counts[START]=4*blank_corner**2
    counts[RIGHT]=blank_corner*(876*blank_corner+176*3*blank_corner+706*headed_corner)
    assert len(counts)==439
    return counts

def next5(n):
    p,e=1,0
    while p<n:p*=5;e+=1
    return p,e

def layout(k,minimal_bands=True,a=A):
    ell=max(2,(k+1).bit_length())
    pad=max(0,(k-2*ell-21*a-3)//2)
    jmax=9*a+4+pad
    m0=2*ell+30*a+8+2*pad
    npos=m0+1
    ndum=npos-k-9*a-4
    estart=k+12*a
    anchor=k+15*a+ndum
    emax=27*anchor
    h=51*anchor+3*a+1
    t1=h+2*emax+a+1
    gap=(4*((emax+1)//2)+2) if minimal_bands else 4*emax+2
    t2=t1+gap
    length,le=next5(t2+2*emax+2)
    u=4*(npos+2)*(28*(k+9*a+4)+6)+8
    bmin=max(ell*(jmax+1)+3,ell*(9*a+4)+u.bit_length()+1,4)
    b,be=next5(bmin)
    assert ndum>=1 and gap>2*emax and gap%4==2
    assert length-gap>emax and t2+emax<length
    # For every H modulo 4, rho=2 modulo 5 and paired clause terms cancel.
    assert all((2*(pow(2,3*a,5)+pow(2,hh+a,5)+2)-pow(2,hh,5))%5==3 for hh in range(4))
    return dict(alphabet=a,windows=k,ell=ell,padding=pad,mu_top=jmax,m=m0,
      native_positions=npos,dummy_count=ndum,dummy_start=estart,anchor_unit=anchor,
      emax=emax,shift_H=h,T1=t1,T2=t2,band_gap=gap,cell_length=length,
      cell_length_power_five=le,radix_threshold=bmin,radix_bits=b,radix_bits_power_five=be,
      cell_bits=b*length,cell_bits_power_five=be+le)

def sparse_compiler_checks():
    """Independent coefficient convolution tests, including shorter clause gaps."""
    cases=[]
    for a,k in ((3,2),(3,3),(3,100),(7,4),(7,201),(11,300)):
        g=layout(k,a=a);radix=1<<g['ell'];M=g['anchor_unit'];E=g['emax'];h=g['shift_H']
        windows=[tuple((i//a**(8-t))%a for t in range(9)) for i in range(k)]
        assert len(set(windows))==k
        def e(r,c,u):return k+3*a+(2-r)*3*a+(2-c)*a+u
        def j(r,c,u):return 1+(3*r+c)*a+u
        weights={i:1+sum(radix**j(r,c,windows[i][3*r+c]) for r,c in product(range(3),repeat=2))
                   +sum(radix**(9*a+t) for t in range(1,5)) for i in range(k)}
        for r,c,u in product(range(3),range(3),range(a)):weights[e(r,c,u)]=radix**j(r,c,u)
        anchors=[M,3*M,9*M,27*M]
        for t,p in enumerate(anchors,1):weights[p]=radix**(9*a+t)
        dummies=list(range(g['dummy_start'],g['dummy_start']+g['dummy_count']))
        for p in dummies:weights[p]=0
        assert len(weights)==g['native_positions']
        DC={}
        def add(e,c=1):DC[e]=DC.get(e,0)+c
        for p in (3*a,h+a,8*M,24*M):add(p)
        for p,w in weights.items():
            if w:
                add(g['T1']-p,w);add(g['T2']-p,w)
        mu=radix-2+sum(radix**t for t in range(1,g['mu_top']+1))
        assert 2*mu.bit_count()+12*a+2==g['m']
        tests=[]
        for t in (g['T1'],g['T2']):tests.append((t,lambda site,p:weights[p] if site==0 else 0))
        for r,c,u in product(range(2),range(3),range(a)):
            target=e(r,c,u);source=e(r+1,c,u)
            tests.append((target,lambda site,p,t=target,s=source:int((site==0 and p==s) or (site==2 and p==t))))
        for r,c,u in product(range(3),range(2),range(a)):
            target=h+e(r,c,u);source=e(r,c+1,u);neighbor=e(r,c,u)
            tests.append((target,lambda site,p,s=source,n=neighbor:int((site==0 and p==s) or (site==1 and p==n))))
        for target,source in ((9*M,M),(27*M,3*M)):
            tests.append((target,lambda site,p,t=target,s=source:int((site==0 and p==s) or (site==2 and p==t))))
        comparisons=0
        for site,p,(target,expect) in product(range(3),weights,tests):
            actual=DC.get(target-p,0) if site==0 else int(target-p==h) if site==1 else int(target==p)
            assert actual==expect(site,p)
            comparisons+=1
        support=set(weights);L=g['cell_length'];extended=support|{dummies[0]+1}
        assert not ({(g['T1']-p)%L for p in extended}&{(g['T2']-p)%L for p in extended})
        assert {(9*M-p)%L for p in support}&{(27*M-p)%L for p in support}=={0}
        assert max(DC)+E<L
        target=max(4*(g['native_positions']+2)*(2*sum(weights.values())+6)+8,2*mu+4,16)
        assert (target-1).bit_length()<=g['radix_bits']
        assert (2*sum(w*pow(2,p,5) for p,w in DC.items())-pow(2,h,5))%5==3
        cases.append(dict(a=a,k=k,comparisons=comparisons,band_gap=g['band_gap'],Emax=E))
    return cases

def simulate(table,steps):
    tape={};pos=state=0;history=[]
    for _ in range(steps+1):
        history.append((dict(tape),pos,state))
        if state==215:return history
        b,move,state=table[state,tape.get(pos,0)]
        tape[pos]=b;pos+=move
    return history

def helical_checks():
    controls=[]
    t=dict(TABLE);t[93,0]=(0,0,215);controls.append(t)
    t=dict(TABLE);t[93,0]=(1,-1,2);t[2,1]=(0,-1,3);t[3,0]=(1,1,215);controls.append(t)
    # Longer control: exercise both extreme margins, repeat halt, independent padding.
    t=dict(TABLE)
    for q in range(93,100):
        for b in (0,1):t[q,b]=(1,-1,q+1)
    for q in range(100,110):
        for b in (0,1):t[q,b]=(0,1,q+1 if q<109 else 215)
    controls.append(t)
    count=0;presentations=0
    for table in controls:
        hist=simulate(table,60);assert hist[-1][2]==215
        lo=min(p for _,p,_ in hist);hi=max(p for _,p,_ in hist)
        # The minimum visited cell lies at least two interior cells from V.
        origin=3-lo
        minwidth=origin+hi+3
        for dw,dh in product(range(5),repeat=2):
            width=minwidth+dw;height=len(hist)+1+dh;n=width*height
            word=[None]*n
            for y,x in product(range(height),range(width)):
                if x==0:code=VERT
                elif y==0:code=HORIZ
                elif y==1:code=LEFT if x<origin else START if x==origin else RIGHT
                else:
                    tape,head,q=hist[min(y-1,len(hist)-1)];b=tape.get(x-origin,0)
                    code=2*(q+1)+b if x-origin==head else b
                j=(-(x-origin)-width*(y-1))%n
                assert word[j] is None;word[j]=code
            blocks=[tuple(word[(j-dx-width*dy)%n] for dy in (-1,0,1) for dx in (-1,0,1)) for j in range(n)]
            assert blocks[0]==S and blocks.count(S)==1 and BAD not in blocks
            assert all(allowed(b,table) for b in blocks)
            for j,b in enumerate(blocks):
                r=blocks[(j-1)%n];down=blocks[(j-width)%n]
                assert all(b[3*y+x+1]==r[3*y+x] for y in range(3) for x in range(2))
                assert all(b[3*(y+1)+x]==down[3*y+x] for y in range(2) for x in range(3))
            count+=n;presentations+=1
    return dict(presentations=presentations,windows_and_overlaps=count,strict_blank_seam_margins=True)

def main():
    digest=sha256(MACHINE.read_bytes()).hexdigest()
    assert digest=='fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
    source=json.loads((DATA/'k215_transitions.json').read_text())
    assert ROWS==list(map(tuple,source['transitions']))
    assert TABLE[0,0]==(1,1,93)
    assert [r for r in ROWS if r[-1]==215]==[(68,1,1,1,215)]
    assert allowed(S) and allowed(BAD)
    count=json.loads((HERE/'count_windows_independent.json').read_text())
    assert count['crosses']==38256607897
    assert count['windows']==1420903358357108792377
    formulas=row_limited_formula()
    assert all(formulas[r['code']]==r['row_head_limited_windows'] for r in count['centers'])
    k=sum(formulas.values());assert k==count['row_head_limited_windows']==10762728984864
    raw=layout(count['windows'],False)
    old=json.loads((DATA/'k215_constants.json').read_text())['constants']['layout']
    assert all(raw[key]==value for key,value in old.items() if key in raw)
    new=layout(k)
    assert new['cell_bits_power_five']==43
    receipt=dict(status='PASS',machine_sha256=digest,transition_rows=430,
      source_table_all_rows_match=True,raw_alphabet=raw,new_alphabet=new,
      cardinality_checks='All 439 center types compared between exhaustive C++ pair enumeration and closed Python formulas.',
      raw_cardinality=count['windows'],row_head_limited_cardinality=k,
      all_center_counts=formulas,helical_checks=helical_checks(),sparse_compiler_checks=sparse_compiler_checks(),
      source_scripts_executed=False,giant_constants_materialized=False,
      proof_assistant_verification=False)
    (HERE/'raw_coefficients_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    spec=dict(schema='k215-row-head-limited-coefficients-v1',
      semantics='All symbols in this document denote specified fixed integers, not existential unknowns.',
      repository='VladimirReshetnikov/ProveIt',
      reviewed_revision='3b201cdea32d2c816f5f3d20734051f25fd3ef14',
      base_package='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/06-blank67',
      machine_sha256=digest,free_parameters=[],
      local_predicate='Clauses 1-6 in RAW_MACHINE_COEFFICIENTS.md; independently implemented as allowed() in raw_coefficients_audit.py.',
      window_order=dict(first=S,second=BAD,rest='All remaining row-major 9-tuples over range(439) satisfying the local predicate, in lexicographic order.'),
      layout=new,
      ports={'Bm1':'B-1','Kconstant':'DC+B*DR','MC':'MC','MF':'MF_native+B-1'},
      definitions={
       'a':'439','kappa':str(k),'A0':'2^ell',
       'mu':'A0-2+sum(A0^j,j=1..mu_top)',
       'e(r,c,u)':'kappa+3a+(2-r)3a+(2-c)a+u; 0<=r,c<=2, 0<=u<a',
       'j(r,c,u)':'1+(3r+c)a+u',
       'Eset':'0..kappa-1; all e(r,c,u); dummy_start..dummy_start+dummy_count-1; M0,3M0,9M0,27M0',
       'M0':'anchor_unit','HC':'shift_H','rho':'2^radix_bits','B':'rho^cell_length=2^cell_bits',
       'c_selector(i)':'1+sum(A0^j(r,c,W_i[3r+c]),r,c=0..2)+sum(A0^(9a+t),t=1..4)',
       'c_copy(e(r,c,u))':'A0^j(r,c,u)',
       'c_anchor(3^(t-1)M0)':'A0^(9a+t), 1<=t<=4','c_dummy':'0',
       'DC':'rho^(3a)+rho^(HC+a)+rho^(8M0)+rho^(24M0)+sum(c_e*(rho^(T1-e)+rho^(T2-e)),e in Eset)',
       'DR':'rho^HC',
       'MF0':'mu*(rho^T1+rho^T2)+sum(rho^e(r,c,u),r=0..1,c=0..2,u=0..a-1)+sum(rho^(HC+e(r,c,u)),r=0..2,c=0..1,u=0..a-1)+rho^(9M0)+rho^(27M0)',
       'MC':'B-1-sum(rho^e,e in Eset except 1)-2*rho^dummy_start',
       'MF_native':'MF0+4'},
      invariants={'2DC_minus_DR_mod5':3,'MC_mod4':2,'MF_native_mod8':4,'mask_population_sum':'cell_bits'},
      expanded_coefficients=False,proof_assistant_verified=False)
    (HERE/'raw_coefficients_specification.json').write_text(json.dumps(spec,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='all_center_counts'},indent=2))

if __name__=='__main__':main()
