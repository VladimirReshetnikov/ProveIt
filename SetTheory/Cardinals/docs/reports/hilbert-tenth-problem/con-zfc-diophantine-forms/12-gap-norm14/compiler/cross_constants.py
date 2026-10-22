#!/usr/bin/env python3
"""Closed coefficients for the cross-window K215 compiler.

All giant constants remain exact finite expressions. The executable audit uses
sparse toy layouts, plus exact actual scalar geometry and the K215 cross count.
This adapts the independently delivered 06-blank67 compiler, with its unused
corner coordinates removed. The arithmetic source ports are unchanged.
"""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path

ALPHABET = 439
CROSS_COUNT = 38256607897
TM_SHA256 = "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090"
# Cross coordinates: prior, left, center, right, following.
SHAPE = ((0,1),(1,0),(1,1),(1,2),(2,1))
VERTICAL = (((0,1),(1,1)),((1,1),(2,1)))
HORIZONTAL = (((1,0),(1,1)),((1,1),(1,2)))
START = (438,434,435,436,1)
EXCLUDED = (438,0,437,438,437)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def next_five_power(n):
    p, e = 1, 0
    while p < n:
        p *= 5
        e += 1
    return p, e


def payload(a,k,r,c,s):
    # Retain the 3x3 geometric grid but use only its cross positions.
    return k+3*a+(2-r)*3*a+(2-c)*a+s


def layout(a,k):
    require(a>=1 and k>=2, "Bad finite alphabet or cross count")
    ell=max(2,(k+1).bit_length())
    p=max(0,(k-2*ell-9*a-4+1)//2)
    mu_top=5*a+4+p
    m=2*ell+14*a+8+2*p
    n=m+1
    nd=n-k-5*a-4
    require(nd>=1,"At least one dummy position is needed")
    es=k+12*a
    M=k+15*a+nd
    emax=27*M
    H=emax+24*M+3*a+1
    T1=H+2*emax+a+1
    T2=T1+4*emax+2
    L,le=next_five_power(T2+2*emax+2)
    U=4*(n+2)*(28*(k+5*a+4)+6)+8
    bmin=max(ell*(mu_top+1)+3,ell*(5*a+4)+U.bit_length()+1,4)
    b,be=next_five_power(bmin)
    require(T2-T1>2*emax and L-(T2-T1)>emax,"Clause bands overlap under rotation")
    require(T2+emax<L,"Field spills across a cell")
    require(es+nd< M,"Payload/dummy/anchor separation failed")
    return dict(alphabet=a,crosses=k,ell=ell,padding=p,mu_top=mu_top,m=m,
        native_positions=n,dummy_count=nd,dummy_start=es,anchor_unit=M,
        emax=emax,shift_H=H,T1=T1,T2=T2,cell_length=L,
        cell_length_power_five=le,radix_bits=b,radix_bits_power_five=be,
        radix_threshold=bmin,cell_bits=b*L,cell_bits_power_five=be+le,
        mask_population_MC=b*L-m-1,mask_population_MF=m+1)


def toy_compiler(crosses,a):
    g=layout(a,len(crosses));k=len(crosses);A=1<<g['ell']
    require(all(len(x)==5 and all(0<=s<a for s in x) for x in crosses),"Malformed crosses")
    coeff={i:1 for i in range(k)}
    mu=A-2
    for z,(r,c) in enumerate(SHAPE):
        for s in range(a):
            j=1+z*a+s; v=A**j; e=payload(a,k,r,c,s)
            coeff[e]=v; mu+=v
            for i,w in enumerate(crosses):
                if w[z]==s:coeff[i]+=v
    anchors=[g['anchor_unit']*x for x in (1,3,9,27)]
    for j,e in enumerate(anchors,5*a+1):
        v=A**j;coeff[e]=v;mu+=v
        for i in range(k):coeff[i]+=v
    for j in range(5*a+5,g['mu_top']+1):mu+=A**j
    dummy=list(range(g['dummy_start'],g['dummy_start']+g['dummy_count']))
    positions=list(range(k))+[payload(a,k,r,c,s) for r,c in SHAPE for s in range(a)]+dummy+anchors
    require(len(set(positions))==g['native_positions'],"Native census")
    require(2*mu.bit_count()+4*a+2==g['m'],"Mask population identity")
    DC={};MF={}
    def add(dic,e,v=1):dic[e]=dic.get(e,0)+v
    for e in (3*a,g['shift_H']+a,8*g['anchor_unit'],24*g['anchor_unit']):add(DC,e)
    for e,v in coeff.items():
        add(DC,g['T1']-e,v);add(DC,g['T2']-e,v)
    add(MF,g['T1'],mu);add(MF,g['T2'],mu)
    for (r,c),_ in VERTICAL:
        for s in range(a):add(MF,payload(a,k,r,c,s))
    for (r,c),_ in HORIZONTAL:
        for s in range(a):add(MF,g['shift_H']+payload(a,k,r,c,s))
    for e in anchors[2:]:add(MF,e)
    require(sum(v.bit_count() for v in MF.values())==g['m'],"Field mask population")
    mass=max(4*(g['native_positions']+2)*(2*sum(coeff.values())+6)+8,2*mu+4,16)
    require(g['radix_bits'] >= (mass-1).bit_length(),"Radix mass bound")
    require(max(DC)+g['emax']<g['cell_length'],"No cell wrap")
    tests=[]
    for t in (g['T1'],g['T2']):tests.append((t,lambda site,e:coeff.get(e,0) if site==0 else 0))
    for (r,c),(r1,c1) in VERTICAL:
        for s in range(a):
            t=payload(a,k,r,c,s);e0=payload(a,k,r1,c1,s)
            tests.append((t,lambda site,e,t=t,e0=e0:int(site==0 and e==e0 or site==2 and e==t)))
    for (r,c),(r1,c1) in HORIZONTAL:
        for s in range(a):
            t=g['shift_H']+payload(a,k,r,c,s)
            e0=payload(a,k,r1,c1,s);e1=payload(a,k,r,c,s)
            tests.append((t,lambda site,e,e0=e0,e1=e1:int(site==0 and e==e0 or site==1 and e==e1)))
    for t,e0 in zip(anchors[2:],anchors[:2]):
        tests.append((t,lambda site,e,t=t,e0=e0:int(site==0 and e==e0 or site==2 and e==t)))
    count=0
    for site,e,(t,expected) in itertools.product(range(3),positions,tests):
        actual=DC.get(t-e,0) if site==0 else int(t-e==g['shift_H']) if site==1 else int(t==e)
        require(actual==expected(site,e),"Convolution basis mismatch")
        count+=1
    support=set(positions);expanded=support|{dummy[0]+1};L=g['cell_length']
    require(not({(g['T1']-e)%L for e in expanded}&{(g['T2']-e)%L for e in expanded}),"No clean clause band")
    common={(anchors[2]-e)%L for e in support}&{(anchors[3]-e)%L for e in support}
    require(common=={0},"Anchor alignment")
    unit=(2*sum(v*pow(2,e,5) for e,v in DC.items())-pow(2,g['shift_H'],5))%5
    if a%4==3:require(unit==3,"Five-adic unit")
    return dict(alphabet=a,crosses=k,basis_checks=count,all_rotation_checks=True,
                unit_mod5=unit,layout=g)


def cross_overlap(c,r,y):
    # Matches two horizontal and two temporal overlaps.
    return c[3]==r[2] and c[2]==r[1] and c[4]==y[2] and c[2]==y[0]


def verify_reconstruction():
    # Exhaust all cyclic binary center words, all strides, lengths 1..8.
    nchecks=0
    for n in range(1,9):
        for word in itertools.product((0,1),repeat=n):
            for h in range(n):
                crosses=[(word[(i+h)%n],word[(i+1)%n],word[i],
                          word[(i-1)%n],word[(i-h)%n]) for i in range(n)]
                require(all(cross_overlap(crosses[i],crosses[(i-1)%n],crosses[(i-h)%n]) for i in range(n)),"Lift overlap failed")
                nchecks+=n
    # Exhaust all sequences of binary crosses for lengths <=3 and all strides.
    # Establish that there are exactly 2^n solutions: one for each center word.
    exhaustive=0
    allcross=list(itertools.product((0,1),repeat=5))
    for n in range(1,4):
        for h in range(n):
            count=0
            for seq in itertools.product(allcross,repeat=n):
                if not all(cross_overlap(seq[i],seq[(i-1)%n],seq[(i-h)%n]) for i in range(n)):continue
                centers=[c[2] for c in seq]
                for i,c in enumerate(seq):
                    require(c==(centers[(i+h)%n],centers[(i+1)%n],centers[i],
                                centers[(i-1)%n],centers[(i-h)%n]),"False cross reconstruction")
                count+=1
            require(count==2**n,"Spurious overlaps or missing lifts")
            exhaustive+=len(allcross)**n
    return dict(lift_checks=nchecks,exhaustive_cross_sequences=exhaustive)


def verify_source(tm_path):
    """Bind the new crosses to the actual source and exercise helical seams.

    The three imported support modules are exact package-06 source copies.
    They are needed only for this optional source audit, not the finite
    coefficient specification or sparse compilation checks.
    """
    import blank_helical as bh
    from verify_k215 import parse_tm
    from count_blank_alphabet import verify as count
    rows=parse_tm(Path(tm_path).read_bytes())
    table=bh.table_from_rows(rows)
    census=count(rows,direct=True)
    require(census['valid_crosses']==CROSS_COUNT,'Pinned cross cardinality')
    project=lambda w:tuple(w[i] for i in (1,3,4,5,7))
    require(project(bh.S)==START and project(bh.E)==EXCLUDED,'Marker binding')
    controls=[]
    first=dict(table);first[93,0]=bh.HALT,0,0;controls.append(first)
    second=dict(table);second[93,0]=2,1,-1;second[2,1]=3,0,-1
    second[3,0]=bh.HALT,1,1;controls.append(second)
    checked=0;presentations=0
    for control in controls:
        history=bh.simulate(control,20)
        require(history[-1][2]==bh.HALT,'Control must halt')
        min_width=max(1,-min(h for _,h,_ in history))+max(1,max(h for _,h,_ in history))+2
        for dw in range(4):
            for dh in range(4):
                grid,x=bh.strip(history,min_width+dw,len(history)+1+dh)
                word=bh.cyclic(grid,x);windows=bh.lift(word,len(grid[0]))
                crosses=list(map(project,windows));n=len(word);stride=len(grid[0])
                for i,c in enumerate(crosses):
                    reduced=[0]*9
                    for j,v in zip((1,3,4,5,7),c):reduced[j]=v
                    require(bh.local_valid(reduced,control),'Cross predicate changed')
                    require(cross_overlap(c,crosses[(i-1)%n],crosses[(i-stride)%n]),'Cross seam overlap')
                require(crosses[0]==START and crosses.count(START)==1,'Canonical Start')
                require(EXCLUDED not in crosses,'Impossible cross')
                checked+=n;presentations+=1
    return dict(machine_sha256=TM_SHA256,valid_crosses=CROSS_COUNT,
                center_categories=len(census['categories']),
                helical_presentations=presentations,helical_crosses=checked)


def specification():
    g=layout(ALPHABET,CROSS_COUNT)
    return dict(schema="proveit-k215-cross-constants-v1",machine_sha256=TM_SHA256,
        representation="Four exact finite-expression integers; no binary expansion allocated",
        free_parameters=[],alphabet=ALPHABET,cross_count=CROSS_COUNT,
        cross_coordinates=["prior","left","center","right","following"],
        cross_order={"first":START,"second":EXCLUDED,
            "rest":"lexicographic 5-tuples in range(439), satisfying local_valid after insertion at positions 1,3,4,5,7 of a zero-corner 3x3 window; exclude first two"},
        geometry=g,definitions={
            "A":"2^ell","mu":"A-2+sum(A^j,j=1..mu_top)",
            "e(r,c,s)":"k+3a+(2-r)3a+(2-c)a+s, (r,c) in [(0,1),(1,0),(1,1),(1,2),(2,1)]",
            "j(z,s)":"1+z*a+s, z=0..4 in the specified shape order",
            "c_i":"1+sum(A^(1+z*a+W_i[z]),z=0..4)+sum(A^(5a+t),t=1..4)",
            "c_e(r,c,s)":"A^(1+z*a+s), with (r,c)=SHAPE[z]",
            "c_(3^(t-1)M)":"A^(5a+t),t=1..4","c_dummy":"0",
            "positions":"0..k-1; all five cross payload blocks; dummy_start..dummy_start+dummy_count-1; M,3M,9M,27M",
            "r":"2^radix_bits","B":"r^cell_length=2^cell_bits",
            "DC":"r^(3a)+r^(H+a)+r^(8M)+r^(24M)+sum(c_e*(r^(T1-e)+r^(T2-e)),e in positions)",
            "DR":"r^H",
            "MF0":"mu*(r^T1+r^T2)+sum(r^e(r0,c,s),(r0,c) in [(0,1),(1,1)],s=0..a-1)+sum(r^(H+e(r0,c,s)),(r0,c) in [(1,0),(1,1)],s=0..a-1)+r^(9M)+r^(27M)",
            "MC":"B-1-sum(r^e,e in positions except1)-2*r^dummy_start",
            "MF_native":"MF0+4","Bm1":"B-1","Kconstant":"DC+B*DR","MF":"MF_native+B-1"},
        polynomial_ports=["Bm1","Kconstant","MC","MF"],
        certificates={"MC_mod4":2,"MF_native_mod8":4,
            "pc_MC_plus_pc_MF":"cell_bits","2DC_minus_DR_mod5":3})


def verify():
    checks=[toy_compiler([(0,)*5,(1,)*5],3),
            toy_compiler([(0,)*5,(1,)*5,(2,)*5],3),
            toy_compiler([(0,)*5,(1,)*5,(2,)*5,(3,)*5],7)]
    return dict(status="PASS",sparse_compilers=checks,reconstruction=verify_reconstruction(),
                actual_giant_constants_materialized=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--tm",type=Path,help="Optional exact K215 table for a direct source/predicate audit")
    args=parser.parse_args()
    result={"constants":specification(),"verification":verify()}
    if args.tm:result['source_verification']=verify_source(args.tm)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"PASS","geometry":result["constants"]["geometry"]},indent=2))
if __name__=="__main__":main()

