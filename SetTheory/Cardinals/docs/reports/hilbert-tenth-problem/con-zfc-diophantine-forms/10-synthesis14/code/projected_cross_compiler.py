#!/usr/bin/env python3
"""Projected-cross coefficient compiler for blank K215; no giant expansion.

The previous-time entry is used only through its H-boundary bit. A tile is
(prior_H, left, center, right, following). A sixth native payload copies
the center's H-bit so the two vertical overlaps remain ordinary equalities.

Derived from 06-blank67/code/compiler_constants.py (MIT-0), ProveIt pin
3b201cdea32d2c816f5f3d20734051f25fd3ef14. See projected_cross_proof.md.
"""
from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

ALPHABET = 439
PROJECTED_CROSS_COUNT = 87_923_161
TM_SHA256 = "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090"
SLOT_NAMES = ("prior_H", "left", "center", "right", "following", "center_H")
START = (1, 434, 435, 436, 1)
EXCLUDED = (1, 0, 437, 438, 437)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def next_five_power(n):
    p, e = 1, 0
    while p < n:
        p *= 5
        e += 1
    return p, e


def slots(a, k):
    """(name, alphabet-size, exponent-offset, clause-exponent-offset)."""
    sizes = (2, a, a, a, a, 2)
    shifts = (10*a, 5*a, 4*a, 3*a, a, 7*a)
    start=0; result=[]
    for name,size,shift in zip(SLOT_NAMES,sizes,shifts):
        result.append((name,size,k+shift,start))
        start+=size
    require(start==4*a+4,"Payload cardinality")
    return tuple(result)


def layout(alphabet, crosses):
    a, k = alphabet, crosses
    require(a >= 3 and k >= 2, "Bad finite alphabet or cross count")
    ell = max(2, (k+1).bit_length())
    padding = max(0, (k-2*ell-7*a-10+1)//2)
    mu_top = 4*a+8+padding
    m = 2*ell+11*a+18+2*padding
    count = m+1
    dummy_count = count-k-4*a-8
    require(dummy_count >= 1,"At least one free dummy is required")
    dummy_start = k+12*a
    anchor = k+15*a+dummy_count
    emax = 27*anchor
    shift_h = emax+24*anchor+3*a+1
    band1 = shift_h+2*emax+a+1
    band2 = band1+4*emax+2
    cell_length, cell_exp = next_five_power(band2+2*emax+2)
    # Selectors: one constant, six payload copies, four anchors.
    prefactor=4*(count+2)*(22*(k+4*a+8)+6)+8
    radix_threshold=max(ell*(mu_top+1)+3,
                        ell*(4*a+8)+prefactor.bit_length()+1,4)
    radix_bits,radix_exp=next_five_power(radix_threshold)
    cell_bits=radix_bits*cell_length
    require(cell_bits==5**(radix_exp+cell_exp),"Power-five dimensions")
    require(band2-band1>2*emax,"Clause bands overlap")
    require(cell_length-(band2-band1)>emax,"Wrapped clause bands overlap")
    require(band2+emax<cell_length,"Field support crosses cells")
    require(dummy_start+1<anchor,"Upper dummy spill reaches an anchor")
    return dict(alphabet=a,crosses=k,ell=ell,padding=padding,mu_top=mu_top,
                m=m,native_positions=count,dummy_count=dummy_count,
                dummy_start=dummy_start,anchor_unit=anchor,emax=emax,
                shift_H=shift_h,T1=band1,T2=band2,
                cell_length=cell_length,cell_length_power_five=cell_exp,
                radix_bits=radix_bits,radix_bits_power_five=radix_exp,
                cell_bits=cell_bits,cell_bits_power_five=radix_exp+cell_exp,
                radix_threshold=radix_threshold,
                mask_population_MC=cell_bits-m-1,mask_population_MF=m+1)


def payload_values(cross,a):
    return tuple(cross)+(int(cross[2]==a-1),)


def projected_of_window(window,H=438):
    return (int(window[1]==H),window[3],window[4],window[5],window[7])


def projected_overlap(center,right,following,H=438):
    return (center[2]==right[1] and center[3]==right[2]
            and int(center[2]==H)==following[0]
            and center[4]==following[2])


def projected_valid(cross,table,local_valid):
    if len(cross)!=5 or cross[0] not in (0,1): return False
    window=[0]*9
    window[1]=438 if cross[0] else 0
    for j,s in zip((3,4,5,7),cross[1:]):window[j]=s
    return local_valid(window,table)


def ordered_projected_crosses(table,local_valid):
    """A finite definition, not executed for the actual large alphabet."""
    require(projected_valid(START,table,local_valid),"Invalid Start")
    require(projected_valid(EXCLUDED,table,local_valid),"Invalid excluded tile")
    yield START
    yield EXCLUDED
    for prior in (0,1):
        for lr in itertools.product(range(ALPHABET),repeat=4):
            cross=(prior,)+lr
            if cross not in (START,EXCLUDED) and projected_valid(cross,table,local_valid):
                yield cross


def projected_count(inherited_count):
    """Exact fiber sizes; input is the independently checked old census."""
    parts=[]
    for part in inherited_count['categories']:
        name=part['name']; old=part['crosses']
        if name in ('V','H'):
            require(old%439==0,"Boundary-fiber divisibility")
            new=2*(old//439); fiber='439 old choices -> 2 H-bits'
        elif name.startswith('initial-'):
            new=old; fiber='1 old choice -> 1 H-bit'
        else:
            require(old%438==0,"Noninitial-fiber divisibility")
            new=old//438; fiber='438 old choices -> 1 H-bit'
        parts.append(dict(name=name,full_crosses=old,projected_crosses=new,fiber=fiber))
    total=sum(p['projected_crosses'] for p in parts)
    require(total==PROJECTED_CROSS_COUNT,"Projected alphabet count mismatch")
    return dict(projected_crosses=total,categories=parts,
                proof="The predecessor is used only through equality with H. Full predecessor fibers have sizes 1 and 438.")


def verify_local_projection(legacy_code,tm_path):
    """Finite marked/seam checks using the exact inherited machine table."""
    sys.path.insert(0,str(Path(legacy_code).resolve()))
    import blank_helical as b
    from verify_k215 import parse_tm
    table=b.table_from_rows(parse_tm(Path(tm_path).read_bytes()))
    require(projected_valid(START,table,b.local_valid),'Projected Start local validity')
    require(projected_valid(EXCLUDED,table,b.local_valid),'Projected excluded-tile validity')
    require(projected_of_window(b.S)==START and projected_of_window(b.E)==EXCLUDED,
            'Distinguished-tile projection')
    # EXCLUDED's prior=H forces this actual predecessor H -> V transition.
    impossible_predecessor=[0]*9
    impossible_predecessor[4]=b.H;impossible_predecessor[7]=b.V
    require(not b.local_valid(impossible_predecessor,table),
            'Excluded tile lacks preceding-cell contradiction')
    control1=dict(table);control1[93,0]=b.HALT,0,0
    control2=dict(table);control2[93,0]=2,1,-1
    control2[2,1]=3,0,-1;control2[3,0]=b.HALT,1,1
    presentations=windows=0
    for control in (control1,control2):
        history=b.simulate(control,20)
        require(history[-1][2]==b.HALT,'Halting control')
        width0=max(1,-min(h for _,h,_ in history))+max(1,max(h for _,h,_ in history))+2
        for dw in range(4):
            for dh in range(4):
                width=width0+dw
                grid,head_column=b.strip(history,width,len(history)+1+dh)
                word=b.cyclic(grid,head_column)
                blocks=b.lift(word,width)
                projected=[projected_of_window(block) for block in blocks]
                require(all(projected_valid(x,control,b.local_valid) for x in projected),
                        'Projected control validity across seams')
                require(all(projected_overlap(projected[i],projected[(i-1)%len(word)],
                                               projected[(i-width)%len(word)])
                            for i in range(len(word))), 'Projected control overlaps')
                require(projected[0]==START and projected.count(START)==1,
                        'Projected canonical Start')
                require(EXCLUDED not in projected,'Excluded tile in valid projected tableau')
                presentations+=1;windows+=len(word)
    history=b.simulate(table,20)
    require(history[-1][2]!=b.HALT,'Unexpected halt in finite prefix')
    width=max(1,-min(h for _,h,_ in history))+max(1,max(h for _,h,_ in history))+2
    grid,head_column=b.strip(history,width,len(history)+1)
    blocks=b.lift(b.cyclic(grid,head_column),width)
    require(not all(projected_valid(projected_of_window(x),table,b.local_valid) for x in blocks),
            'Nonhalting truncation accepted after projection')
    return dict(status='PASS',machine_sha256=TM_SHA256,
                start_and_excluded_locally_valid=True,
                excluded_predecessor_vertical_contradiction=True,
                halting_control_presentations=presentations,
                projected_windows_and_overlaps=windows,
                actual_nonhalting_prefix_rejected_steps=20,
                scope='Finite checks; arbitrary-run theorem is proved in the manuscript')


def interval_support_certificate(a,k):
    """Exact support audit at the actual dimensions using only intervals.

    This proves every basis-vector incidence without listing any selector.
    The enormous coefficients need not be evaluated: clause-band incidences
    are the diagonal e=e' by separation, and are otherwise identically zero.
    """
    g=layout(a,k);M=g['anchor_unit'];H=g['shift_H'];E=g['emax']
    support=[('selectors',0,k-1)]
    support += [(name,base,base+size-1) for name,size,base,_ in slots(a,k)]
    support += [('dummy',g['dummy_start'],g['dummy_start']+g['dummy_count']-1)]
    support += [(f'anchor{u}',u*M,u*M) for u in (1,3,9,27)]
    require(all(hi<M for name,lo,hi in support if not name.startswith('anchor')),
            'Nonanchors reach first anchor')
    def intersection(a0,a1,b0,b1):
        lo,hi=max(a0,b0),min(a1,b1)
        return (lo,hi) if lo<=hi else None
    def hits(lo,hi,shifts):
        out=[]
        for shift_name,delta in shifts:
            for name,l,h in support:
                overlap=intersection(lo-delta,hi-delta,l,h)
                if overlap is not None:out.append((shift_name,name,*overlap))
        return out
    DCfixed=[('vertical',3*a),('horizontal',H+a),('anchor1',8*M),('anchor2',24*M)]
    targets=[
        ('center_vertical',k+4*a,k+5*a-1,('vertical','following',k+a,k+2*a-1)),
        ('prior_vertical',k+10*a,k+10*a+1,('vertical','center_H',k+7*a,k+7*a+1)),
        ('left_horizontal',H+k+5*a,H+k+6*a-1,('horizontal','center',k+4*a,k+5*a-1)),
        ('center_horizontal',H+k+4*a,H+k+5*a-1,('horizontal','right',k+3*a,k+4*a-1)),
        ('anchor9',9*M,9*M,('anchor1','anchor1',M,M)),
        ('anchor27',27*M,27*M,('anchor2','anchor3',3*M,3*M)),
    ]
    checked=[]
    for name,lo,hi,expected in targets:
        got=hits(lo,hi,DCfixed)
        require(got==[expected],f'Actual-dimensional DC incidence: {name}')
        # Clause bands cannot touch these tests under any source exponent.
        require(hi<g['T1']-E,f'Clause contamination: {name}')
        checked.append(dict(test=name,source=expected))
    require(hits(H+k+5*a,H+k+6*a-1,[('right',H)])==[('right','left',k+5*a,k+6*a-1)],
            'Right-neighbor left incidence')
    require(hits(H+k+4*a,H+k+5*a-1,[('right',H)])==[('right','center',k+4*a,k+5*a-1)],
            'Right-neighbor center incidence')
    for name,lo,hi,_ in targets:
        if not name.endswith('horizontal'):
            require(not hits(lo,hi,[('right',H)]),'Spurious right-neighbor incidence')
    for band in (g['T1'],g['T2']):
        require(band>max(delta for _,delta in DCfixed)+E,'Fixed clause contamination')
        require(band>H+E,'Right-neighbor clause contamination')
    require(g['T2']-g['T1']>2*E,'Cross-clause contamination')
    require(g['cell_length']-(g['T2']-g['T1'])>E,'Wrapped clause-band collision')
    pairs=[]
    for name1,lo1,hi1 in support:
        for name2,lo2,hi2 in support:
            iv=intersection(lo1,hi1,lo2-18*M,hi2-18*M)
            if iv is not None:pairs.append((name1,name2,*iv))
    require(pairs==[('anchor9','anchor27',9*M,9*M)],'Anchor pair alignment')
    require(g['cell_length']>45*M,'Wrapped anchor pair')
    return dict(status='PASS',dimension_scope='actual K215 projected-cross layout',
                fixed_field_incidences=checked,anchor_pair=pairs,
                selector_intervals_enumerated=False,giant_coefficients_evaluated=False,
                proof_method='Exact integer interval intersections and band separation')


def toy_compiler(crosses,a):
    require(all(len(x)==5 and x[0] in (0,1) and all(0<=s<a for s in x[1:]) for x in crosses),
            "Bad toy projected crosses")
    k=len(crosses);g=layout(a,k);A=1<<g['ell'];slot_info=slots(a,k)
    coeff={i:1 for i in range(k)};mu=A-2
    for t,(_,size,base,jbase) in enumerate(slot_info):
        for s in range(size):
            j=1+jbase+s;v=A**j;e=base+s
            coeff[e]=v;mu+=v
            for i,cross in enumerate(crosses):
                if payload_values(cross,a)[t]==s:coeff[i]+=v
    anchors=[g['anchor_unit']*x for x in (1,3,9,27)]
    for j,e in enumerate(anchors,4*a+5):
        v=A**j;coeff[e]=v;mu+=v
        for i in range(k):coeff[i]+=v
    for j in range(4*a+9,g['mu_top']+1):mu+=A**j
    dummy=list(range(g['dummy_start'],g['dummy_start']+g['dummy_count']))
    positions=list(range(k))+[base+s for _,size,base,_ in slot_info
                              for s in range(size)]+dummy+anchors
    require(len(set(positions))==g['native_positions'],"Native census")
    require(2*mu.bit_count()+3*a+4==g['m'],"Mask population formula")
    DC={};MF={}
    def add(d,e,c=1):d[e]=d.get(e,0)+c
    for e in (3*a,g['shift_H']+a,8*g['anchor_unit'],24*g['anchor_unit']):add(DC,e)
    for e,v in coeff.items():add(DC,g['T1']-e,v);add(DC,g['T2']-e,v)
    add(MF,g['T1'],mu);add(MF,g['T2'],mu)
    # vertical targets: center/full (a) and prior/H-bit (2)
    for base,size in ((k+4*a,a),(k+10*a,2)):
        for s in range(size):add(MF,base+s)
    # horizontal targets: left/full and center/full
    for base in (k+5*a,k+4*a):
        for s in range(a):add(MF,g['shift_H']+base+s)
    for e in anchors[2:]:add(MF,e)
    require(sum(v.bit_count() for v in MF.values())==g['m'],"MF population")
    mass=max(4*(g['native_positions']+2)*(2*sum(coeff.values())+6)+8,2*mu+4,16)
    require(g['radix_bits'] >= (mass-1).bit_length(),"Radix mass bound")
    require(max(DC)+g['emax']<g['cell_length'],"No field wrap")
    tests=[]
    for t in (g['T1'],g['T2']):tests.append((t,lambda site,e:coeff.get(e,0) if site==0 else 0))
    for base,size in ((k+4*a,a),(k+10*a,2)):
        for s in range(size):
            t=base+s;e0=t-3*a
            tests.append((t,lambda site,e,t=t,e0=e0:
                          int(site==0 and e==e0 or site==2 and e==t)))
    for base in (k+5*a,k+4*a):
        for s in range(a):
            t=g['shift_H']+base+s;e0=base+s-a;e1=base+s
            tests.append((t,lambda site,e,e0=e0,e1=e1:
                          int(site==0 and e==e0 or site==1 and e==e1)))
    for t,e0 in zip(anchors[2:],anchors[:2]):
        tests.append((t,lambda site,e,t=t,e0=e0:
                      int(site==0 and e==e0 or site==2 and e==t)))
    count=0
    for site,e,(t,expected) in itertools.product(range(3),positions,tests):
        actual=DC.get(t-e,0) if site==0 else int(t-e==g['shift_H']) if site==1 else int(t==e)
        require(actual==expected(site,e),"Convolution basis mismatch")
        count+=1
    support=set(positions);expanded=support|{dummy[0]+1};L=g['cell_length']
    require(not({(g['T1']-e)%L for e in expanded}
                &{(g['T2']-e)%L for e in expanded}),"No clean band")
    common={(anchors[2]-e)%L for e in support}&{(anchors[3]-e)%L for e in support}
    require(common=={0},"Anchor alignment fails")
    unit=(2*sum(v*pow(2,e,5) for e,v in DC.items())-pow(2,g['shift_H'],5))%5
    if a%4==3:require(unit==3,"Uniform five-adic unit")
    return dict(alphabet=a,projected_crosses=k,basis_checks=count,
                all_rotation_band_and_anchor_checks=True,unit_mod5=unit,layout=g)


def verify():
    examples=[toy_compiler([(0,0,0,0,0),(1,1,1,1,1)],3),
              toy_compiler([(0,0,0,0,0),(1,1,1,1,1),(0,2,2,2,2)],3),
              toy_compiler([(0,0,0,0,0),(1,1,1,1,1),(0,6,6,6,6),(1,3,3,3,3)],7),
              toy_compiler([(0,0,1,2,0),(1,1,2,0,1),(0,2,0,1,2)],3)]
    for a in range(3,80,4):
        for h in range(4):
            require((2*(pow(2,3*a,5)+pow(2,h+a,5)+2)-pow(2,h,5))%5==3,
                    "Five-adic identity")
    checked=0
    for n in range(1,8):
        for h in range(n):
            for word in itertools.product(range(2),repeat=n):
                xs=[(word[(i+h)%n],word[(i+1)%n],word[i],word[(i-1)%n],word[(i-h)%n])
                    for i in range(n)]
                require(all(projected_overlap(xs[i],xs[(i-1)%n],xs[(i-h)%n],H=1)
                            for i in range(n)),"Projected lift identity")
                checked+=1
    g=layout(ALPHABET,PROJECTED_CROSS_COUNT)
    require(g['radix_bits_power_five']==13 and g['cell_length_power_five']==15
            and g['cell_bits_power_five']==28,"Actual scalar geometry")
    return dict(status="PASS",toy_sparse_compilers=examples,
                projected_reconstruction_checks=checked,
                actual_dimension_support=interval_support_certificate(ALPHABET,PROJECTED_CROSS_COUNT),
                actual_giant_crosses_or_numerals_materialized=False,
                scope="Finite implementation checks; universal equivalence is proved separately.")


def specification():
    g=layout(ALPHABET,PROJECTED_CROSS_COUNT)
    return dict(schema="proveit-k215-projected-cross-constants-v1",
                representation="closed finite integer expressions; expansions not materialized",
                free_parameters=[],machine_sha256=TM_SHA256,
                alphabet_size=ALPHABET,projected_cross_count=PROJECTED_CROSS_COUNT,
                slot_order=SLOT_NAMES,slot_data=slots(ALPHABET,PROJECTED_CROSS_COUNT),
                cross_order={"first":START,"second":EXCLUDED,
                  "rest":"lexicographic tuples in {0,1} x range(439)^4 satisfying projected_valid, excluding first two"},
                layout=g,
                definitions={
                  "a":"alphabet_size","k":"projected_cross_count","M":"anchor_unit","A":"2^ell",
                  "mu":"A-2+sum(A^j,j=1..mu_top)",
                  "payload_e(t,s)":"slot_data[t].exponent_offset+s",
                  "payload_j(t,s)":"1+slot_data[t].clause_exponent_offset+s",
                  "payload_value(i,t)":"W_i[t] for t<5; int(W_i[2]==438) for t=5",
                  "c_selector(i)":"1+sum(A^payload_j(t,payload_value(i,t)),t=0..5)+sum(A^(4*a+4+u),u=1..4)",
                  "c_payload(t,s)":"A^payload_j(t,s)",
                  "c_anchor(u)":"A^(4*a+4+u),u=1..4","c_dummy":"0",
                  "positions":"selectors 0..k-1; all six payload slots; dummy_start..dummy_start+dummy_count-1; M,3M,9M,27M",
                  "rho":"2^radix_bits","B":"rho^cell_length=2^cell_bits",
                  "DC":"rho^(3*a)+rho^(shift_H+a)+rho^(8*M)+rho^(24*M)+sum(c_e*(rho^(T1-e)+rho^(T2-e)),e in positions)",
                  "DR":"rho^shift_H",
                  "MF0":"mu*(rho^T1+rho^T2)+sum(rho^(k+4*a+s),s=0..a-1)+sum(rho^(k+10*a+s),s=0..1)+sum(rho^(shift_H+k+u*a+s),u=4..5,s=0..a-1)+rho^(9*M)+rho^(27*M)",
                  "MC":"B-1-sum(rho^e,e in positions except1)-2*rho^dummy_start",
                  "MF_native":"MF0+4","Bm1":"B-1","Kconstant":"DC+B*DR",
                  "MF":"MF_native+B-1"},
                polynomial_ports=["Bm1","Kconstant","MC","MF"],
                key_certificates={"uniform_unit_2DC_minus_DR_mod5":3,"MC_mod4":2,
                  "MF_native_mod8":4,"native_mask_population_sum":"cell_bits",
                  "bit_length_Bm1":"cell_bits"},
                inherited_endpoint="KEndpoint215.blank_halts_iff_zfc_refutation",
                formal_status="Mathematical proof and finite checks; no new Lean/Rocq theorem")


def main():
    ap=argparse.ArgumentParser(description=__doc__,
        epilog='Relative file arguments are resolved from the archive root, independently of the working directory.')
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--inherited-count',type=Path)
    ap.add_argument('--legacy-code',type=Path)
    ap.add_argument('--tm',type=Path)
    args=ap.parse_args()
    package_root=Path(__file__).resolve().parents[1]
    for name in ('output','inherited_count','legacy_code','tm'):
        value=getattr(args,name)
        if value is not None and not value.is_absolute():
            setattr(args,name,package_root/value)
    result={"constants":specification(),"verification":verify()}
    if args.inherited_count:
        result['projected_count']=projected_count(json.loads(args.inherited_count.read_text()))
    if args.legacy_code or args.tm:
        require(args.legacy_code is not None and args.tm is not None,
                'Both --legacy-code and --tm are required for local projection checks')
        result['local_projection']=verify_local_projection(args.legacy_code,args.tm)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"PASS","geometry":result['constants']['layout'],
                      "constant_expansions_materialized":False}))


if __name__=='__main__':main()
