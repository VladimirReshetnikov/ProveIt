#!/usr/bin/env python3
"""Exact finite-expression constants for the fixed K215 polynomial.

The four constants are fully specified, but not expanded in binary.  In
particular B has d+1 bits, where d is the explicitly computed power of five
in the output.  This module never allocates B, nor the 1.4e21-window list.
The manuscript gives the closed finite sums represented by this recipe.
Toy checks test the new band spacing independently of the giant instance.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path

ALPHABET = 439
WINDOW_COUNT = 1420903358357108792377
CROSS_COUNT = 38256607897
TM_SHA256 = "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090"
START = [438,438,438,434,435,436,0,1,188]
EXCLUDED = [0,438,0,0,437,438,0,437,0]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def next_five_power(n):
    p, e = 1, 0
    while p < n:
        p *= 5
        e += 1
    return p, e


def layout(alphabet, windows):
    """All scalar geometry, without any support or huge coefficient list."""
    a, k = alphabet, windows
    require(a >= 1 and k >= 2, "Bad finite alphabet or window count")
    ell = max(2, (k+1).bit_length())
    # mu=A-2 + sum(A^j, j=1..9*a+4+p); its population is ell+9*a+3+p.
    padding = max(0, (k-2*ell-21*a-4+1)//2)
    mu_top = 9*a+4+padding
    m = 2*ell+30*a+8+2*padding
    count = m+1
    dummy_count = count-k-9*a-4
    require(dummy_count >= 1, "At least one free dummy is required")
    dummy_start = k+12*a
    anchor = k+15*a+dummy_count
    emax = 27*anchor
    shift_h = emax+24*anchor+3*a+1
    band1 = shift_h+2*emax+a+1
    band2 = band1+4*emax+2
    cell_length, cell_exp = next_five_power(band2+2*emax+2)
    # sum(c_e) <= 14*(k+9*a+4)*A^(9*a+4).
    prefactor = 4*(count+2)*(28*(k+9*a+4)+6)+8
    radix_threshold = max(ell*(mu_top+1)+3,
                          ell*(9*a+4)+prefactor.bit_length()+1, 4)
    radix_bits, radix_exp = next_five_power(radix_threshold)
    cell_bits = radix_bits*cell_length
    require(cell_bits == 5**(radix_exp+cell_exp), "Power-five dimensions")
    require(band2-band1 > 2*emax, "Clause bands overlap")
    require(cell_length-(band2-band1) > emax, "Wrapped clause bands overlap")
    require(band2+emax < cell_length, "Field support crosses cells")
    require(dummy_start+1 < emax, "Upper dummy spill reaches an anchor")
    return dict(alphabet=a,windows=k,ell=ell,padding=padding,mu_top=mu_top,
                m=m,native_positions=count,dummy_count=dummy_count,
                dummy_start=dummy_start,anchor_unit=anchor,emax=emax,
                shift_H=shift_h,T1=band1,T2=band2,
                cell_length=cell_length,cell_length_power_five=cell_exp,
                radix_bits=radix_bits,radix_bits_power_five=radix_exp,
                cell_bits=cell_bits,cell_bits_power_five=radix_exp+cell_exp,
                radix_threshold=radix_threshold,
                mask_population_MC=cell_bits-m-1,mask_population_MF=m+1)


def payload(a,k,r,c,s):
    return k+3*a+(2-r)*3*a+(2-c)*a+s


def toy_compiler(windows, a):
    """Finite sparse version of precisely the manuscript's revised recipe."""
    g=layout(a,len(windows)); k=len(windows); A=1<<g['ell']
    coeff={j:1 for j in range(k)}
    mu=A-2
    for r,c,s in itertools.product(range(3),range(3),range(a)):
        j=1+(3*r+c)*a+s; v=A**j; e=payload(a,k,r,c,s)
        coeff[e]=v; mu+=v
        for i,w in enumerate(windows):
            if w[3*r+c]==s: coeff[i]+=v
    anchors=[g['anchor_unit']*x for x in (1,3,9,27)]
    for j,e in enumerate(anchors,9*a+1):
        v=A**j; coeff[e]=v; mu+=v
        for i in range(k): coeff[i]+=v
    for j in range(9*a+5,g['mu_top']+1): mu+=A**j
    dummy=list(range(g['dummy_start'],g['dummy_start']+g['dummy_count']))
    positions=list(range(k))+[payload(a,k,r,c,s) for r,c,s in
              itertools.product(range(3),range(3),range(a))]+dummy+anchors
    require(len(set(positions))==g['native_positions'],"Native census")
    require(2*mu.bit_count()+12*a+2==g['m'],"Mask population formula")
    DC={}; MF={}
    def add(d,e,c=1): d[e]=d.get(e,0)+c
    for e in (3*a,g['shift_H']+a,8*g['anchor_unit'],24*g['anchor_unit']):add(DC,e)
    for e,v in coeff.items():
        add(DC,g['T1']-e,v);add(DC,g['T2']-e,v)
    add(MF,g['T1'],mu);add(MF,g['T2'],mu)
    for r,c,s in itertools.product(range(2),range(3),range(a)):add(MF,payload(a,k,r,c,s))
    for r,c,s in itertools.product(range(3),range(2),range(a)):add(MF,g['shift_H']+payload(a,k,r,c,s))
    for e in anchors[2:]:add(MF,e)
    require(sum(v.bit_count() for v in MF.values())==g['m'],"MF population")
    require(g['radix_bits'] >= (max(4*(g['native_positions']+2)*(2*sum(coeff.values())+6)+8,2*mu+4,16)-1).bit_length(),"Radix mass bound")
    require(max(DC)+g['emax'] < g['cell_length'],"No field wrap")
    tests=[]
    for t in (g['T1'],g['T2']):tests.append((t,lambda site,e:coeff.get(e,0) if site==0 else 0))
    for r,c,s in itertools.product(range(2),range(3),range(a)):
        t=payload(a,k,r,c,s);e0=payload(a,k,r+1,c,s)
        tests.append((t,lambda site,e,t=t,e0=e0:int(site==0 and e==e0 or site==2 and e==t)))
    for r,c,s in itertools.product(range(3),range(2),range(a)):
        t=g['shift_H']+payload(a,k,r,c,s);e0=payload(a,k,r,c+1,s);e1=payload(a,k,r,c,s)
        tests.append((t,lambda site,e,e0=e0,e1=e1:int(site==0 and e==e0 or site==1 and e==e1)))
    for t,e0 in zip(anchors[2:],anchors[:2]):
        tests.append((t,lambda site,e,t=t,e0=e0:int(site==0 and e==e0 or site==2 and e==t)))
    count=0
    for site,e,(t,expected) in itertools.product(range(3),positions,tests):
        actual=DC.get(t-e,0) if site==0 else int(t-e==g['shift_H']) if site==1 else int(t==e)
        require(actual==expected(site,e),"Convolution basis mismatch")
        count+=1
    support=set(positions);expanded=support|{dummy[0]+1};L=g['cell_length']
    # Intersections of shift sets give exact all-rotation checks, without looping L times.
    require(not({(g['T1']-e)%L for e in expanded}&{(g['T2']-e)%L for e in expanded}),"No clean band")
    common={(anchors[2]-e)%L for e in support}&{(anchors[3]-e)%L for e in support}
    require(common=={0},"Anchor alignment fails")
    correction_unit=(2*sum(v*pow(2,e,5) for e,v in DC.items())-pow(2,g['shift_H'],5))%5
    if a%4==3:require(correction_unit==3,"Uniform five-adic unit")
    return dict(alphabet=a,windows=k,basis_checks=count,
                all_rotation_band_and_anchor_checks=True,
                unit_mod5=correction_unit,layout=g)


def verify():
    examples=[toy_compiler([(0,)*9,(1,)*9],3),
              toy_compiler([(0,)*9,(1,)*9,(2,)*9],3),
              toy_compiler([(0,)*9,(1,)*9,(2,)*9,(3,)*9],7)]
    # The 5-adic identity holds for all possible H and all alphabets 3 mod4.
    for a in range(3,80,4):
        for h in range(4):
            require((2*(pow(2,3*a,5)+pow(2,h+a,5)+2)-pow(2,h,5))%5==3,"5-adic identity")
    require(CROSS_COUNT*ALPHABET**4==WINDOW_COUNT,"Exact cardinality")
    return dict(status="PASS",toy_sparse_compilers=examples,
                actual_giant_windows_or_numerals_materialized=False,
                scope="Exact sparse layout checks supplement the parametric support and congruence proofs.")


def specification():
    g=layout(ALPHABET,WINDOW_COUNT)
    return dict(schema="proveit-k215-closed-finite-constants-v1",
                representation="closed finite integer expressions; binary expansions intentionally not materialized",
                free_parameters=[], machine_sha256=TM_SHA256,
                alphabet_size=ALPHABET,valid_crosses=CROSS_COUNT,
                window_count=WINDOW_COUNT,window_order={"first":START,"second":EXCLUDED,
                  "rest":"lexicographic row-major 9-tuples over range(439) satisfying blank_helical.local_valid, excluding the first two"},
                layout=g,
                definitions={
                  "a":"alphabet_size", "k":"window_count", "M":"anchor_unit",
                  "A":"2^ell",
                  "mu":"A-2 + sum(A^j, j=1..mu_top)",
                  "payload_e(r,c,s)":"k+3*a+(2-r)*3*a+(2-c)*a+s",
                  "payload_j(r,c,s)":"1+(3*r+c)*a+s",
                  "c_selector(i)":"1 + sum(A^payload_j(r,c,w_i[3*r+c]), r,c=0..2) + sum(A^(9*a+t),t=1..4)",
                  "c_payload(r,c,s)":"A^payload_j(r,c,s)",
                  "c_anchor(t)":"A^(9*a+t),t=1..4",
                  "c_dummy":"0",
                  "positions":"selectors 0..k-1; all payload_e; dummy_start..dummy_start+dummy_count-1; M,3M,9M,27M",
                  "r":"2^radix_bits", "B":"r^cell_length = 2^cell_bits",
                  "DC":"r^(3*a)+r^(shift_H+a)+r^(8*M)+r^(24*M)+sum(c_e*(r^(T1-e)+r^(T2-e)),e in positions)",
                  "DR":"r^shift_H",
                  "MF0":"mu*(r^T1+r^T2)+sum(r^payload_e(r0,c,s),r0=0..1,c=0..2,s=0..a-1)+sum(r^(shift_H+payload_e(r0,c,s)),r0=0..2,c=0..1,s=0..a-1)+r^(9*M)+r^(27*M)",
                  "MC":"B-1-sum(r^e,e in positions except1)-2*r^dummy_start",
                  "MF_native":"MF0+4",
                  "Bm1":"B-1", "Kconstant":"DC+B*DR", "MF":"MF_native+B-1"},
                polynomial_ports=["Bm1","Kconstant","MC","MF"],
                key_certificates={"uniform_unit_2DC_minus_DR_mod5":3,
                  "MC_mod4":2,"MF_native_mod8":4,
                  "native_mask_population_sum":"cell_bits",
                  "bit_length_Bm1":"cell_bits"},
                evaluation_warning="The recipe defines four specific integers, not an arbitrary four-parameter family. Expanding these integers is not computationally feasible.")


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    result={"constants":specification(),"verification":verify()}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"PASS","geometry":result['constants']['layout'],
                      "constant_expansions_materialized":False}))


if __name__=='__main__':main()
