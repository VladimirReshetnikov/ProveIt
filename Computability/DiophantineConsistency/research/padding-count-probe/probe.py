#!/usr/bin/env python3
"""Complete finite exploration of the padding-staircase C1005/L2011 tuple."""
import argparse
import hashlib
import importlib.util
import json
from math import gcd
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PARENT = ROOT / 'research/phase-split-independent/certify.py'
PARENT_SHA = 'd7f42234adce10ee050168ebdced4a08b2d2c109910967c17b8b0038b61110ef'
RHO, M, A, CENTER, L = 1 << 47, 1 << 45, 1004, 1005, 2011
D = 47 * L


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def sha(value):
    return hashlib.sha256(value).hexdigest()


def source():
    require(sha(PARENT.read_bytes()) == PARENT_SHA, 'Exact reviewed2471 source before import')
    spec = importlib.util.spec_from_file_location('frozen_phase_split2471', PARENT)
    require(spec is not None and spec.loader is not None, 'Valid authenticated source module')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    parent, seed, actions, tiles, c, support = module.model()
    return module, parent, seed, actions, tiles, c, support


def run():
    module, parent, seed, actions, tiles, c, support = source()
    spec = {**module.SPEC, 'centers': [CENTER], 'zero_tail': 2010}
    require(support == set(range(951)) | set(range(960, 986)) | {A}, 'Entire physical support')
    require(len(c) == 3297 and max(c) < M and all(v % 2 == 0 for v in c)
            and sum(c[942:]) == M - 2048, 'Entire unchanged doubled coefficient array')
    require(sum(c[459:]) == 137820284543942 and sum(c[458:]) == 140981380502472,
            'Complete retained suffixes including all labels')
    dc = {CENTER - e: value for e, value in enumerate(c) if value}
    for e in (18, A):
        dc[e] = dc.get(e, 0) + 1
    require(dc == module.dc_coefficients(c, spec) and min(dc) == 18
            and min(CENTER-e for e,v in enumerate(c) if v) == 20
            and dc[A] == c[1] + 1 and all(v < RHO for v in dc.values()),
            'Whole direct kernel, first reflection and marker collision')

    def hits(h):
        return sorted((e, dc[h-e]) for e in support if h-e in dc)

    def parity(h):
        return [(e, v % 2) for e,v in hits(h) if v % 2]

    def reflected(h):
        return [(e, CENTER-h+e, c[CENTER-h+e]) for e in sorted(support)
                if 0 <= CENTER-h+e < len(c) and c[CENTER-h+e]]

    last = max(dc) + A
    envelope = [sum(v for _,v in hits(h)) for h in range(last+1)]
    require(max(envelope) + 1 + RHO//2 + 57 < 58*RHO,
            'Complete Boolean local convolution plus spatial/temporal contribution has global carry57')
    low_rows = []
    for h in range(A):
        terms = reflected(h)
        selector = [(e,index,v) for e,index,v in terms if e < 942]
        controls = [(e,index,v) for e,index,v in terms if e >= 942]
        require(all(index >= 944 for _,index,_ in controls)
                and sum(v for _,_,v in controls) <= M-2048,
                'All reset-band control-source weights lie among the entire doubled label coefficients')
        conditional = max((v for _,_,v in selector), default=0) + sum(v for _,_,v in controls)
        require(conditional + 3 + RHO//2 + 57 < RHO,
                'Every reset-band field resets after at most one selector, with arbitrary Boolean controls')
        low_rows.append((h, terms, conditional))
    require((M-1)+(M-2048)+3+RHO//2+57 < RHO,
            'Uniform conditional bound independent of individual low-field maxima')

    first, endpoint = CENTER-941, CENTER-459
    require((first,endpoint) == (64,546) and endpoint-first+1 == 483
            and 1 <= first <= endpoint <= 916 and endpoint < A,
            'All483 consecutive staircase tests are actual padding fields below the bare marker')
    early_rows, stair_rows = [], []
    for h in range(endpoint+1):
        terms = reflected(h)
        require(all(index >= 459 for _,index,_ in terms)
                and sum(v for _,_,v in terms) <= sum(c[459:])
                and sum(v for _,_,v in terms)+3+1024+57 < RHO,
                'Every early outgoing carry, including the staircase predecessor, vanishes for phases7..10')
        early_rows.append((h,terms))
        if h >= first:
            selector_terms = [(e,index,v) for e,index,v in terms if index < 942]
            require([e for e,_,_ in selector_terms] == list(range(h-first+1))
                    and all(v % 2048 == 2 for _,_,v in selector_terms)
                    and all(v % 2048 == 0 for _,index,v in terms if index >= 942),
                    'Exact prefix of selectors contributes2 each; every other reflected coefficient contributes0 modulo2048')
            require(h-A < 0 and all(e < 942 for e,_,_ in selector_terms),
                    'No marker unit or control source enters the selector prefix')
            stair_rows.append((h,[e for e,_,_ in selector_terms]))
    stair_controls = []
    for phase in range(7,11):
        reachable = {0}
        for step in range(483):
            following = {count+bit for count in reachable for bit in (0,1)
                         for units in range(3) for temporal in (0,1)
                         if ((2*(count+bit)+units+(1<<phase)*temporal) % RHO) & 8 == 0}
            require(following <= {0,1,2,3}, 'Every staircase step excludes the first prefix count4')
            reachable = following
        require(reachable == {0,1,2,3}, 'Complete483-step staircase bound is exact for the residue overapproximation')
        stair_controls.append({'phase':phase,'steps':483,'reachable_counts':sorted(reachable)})
    require(942-483+3 == 462, 'Complete selector count after the prefix bound')
    phase_rows = []
    for phase in range(47):
        nmax = 462 if 7 <= phase <= 10 else 942
        survivors = [(n,k,b,t) for n in range(nmax+1) for k in range(58)
                     for b in (0,1) for t in (0,1)
                     if ((2*n+k+b+(1<<phase)*t) % RHO) & 2044 == 0]
        require(survivors and max(row[0] for row in survivors) == 1,
                'Every fractional phase yields at most one selector, in its stated dependency regime')
        if phase <= 10:
            require(2*nmax+57+1+(1<<phase) <= 2006 < 2048,
                    'Complete bounded low part does not wrap before low-bit decoding')
        else:
            require((1<<phase)%2048 == 0 and 2*942+57+1 == 1942 < 2048,
                    'Large temporal phase disappears in the low eleven-bit count')
        phase_rows.append({'phase':phase,'count_bound_before_clause':nmax,
                           'tested_quadruples':(nmax+1)*58*4,'survivors':survivors})
    require(all((1<<phase)%2 == 0 for phase in range(1,47))
            and parity(A) == [(0,1)] and A-9 not in support,
            'With all low resets proved, the forced marker parity excludes every nonzero fractional phase')

    copy_rows = []
    for j in range(9):
        h = 960+j
        require(parity(h) == [(942+j,1)] and h-9 not in support,
                'Exact temporal-copy odd parts including the full even reflected background')
        copy_rows.append((h,hits(h),None))
    for j in range(8):
        h = 987+j
        require(parity(h) == [(969+j,1)] and h-9 == 978+j and h not in support,
                'Exact spatial-copy odd parts and absence of aligned temporal source')
        copy_rows.append((h,hits(h),h-9))
    clause = {e:c[e] for e in support if c[e]}
    clause[1] += 1
    adjacent = {e:c[e+1] for e in support if c[e+1]}
    adjacent[0] = adjacent.get(0,0)+1
    require(hits(CENTER) == sorted(clause.items()) and CENTER-9 not in support and CENTER not in support,
            'Complete clause1005 is reflected clause plus Boolean selector1 with no aligned temporal/spatial term')
    require(hits(CENTER-1) == sorted(adjacent.items()) and CENTER-1 == A
            and A in support and A-9 not in support,
            'Predecessor1004 is exactly adjacency plus Start selector0 plus aligned temporal marker')
    adj_bound = max(c[e+1] for e in support if e<942) + sum(c[e+1] for e in support if e>=942)
    require(adj_bound <= 2*M-2048 and adj_bound+2+57 < RHO,
            'Aligned predecessor resets even with both Start/temporal-marker Boolean contributions')
    require(all((M+2+bare)&(M-4) == 0 for bare in (0,1)), 'Every canonical occupied clause value passes')

    padding_rows = []
    for h in range(1,917):
        terms = reflected(h)
        require(all(0<=e<=896 and e<942 and v%2048 in (0,2) for e,_,v in terms),
                'Every complete padding reflection has a selector source and residue0 or2')
        units = int(h-18 in support)+int(h-9 in support)+int(h in support)
        require(max((v%2048 for _,_,v in terms),default=0)+units <= 5,
                'After one-hot decoding all aligned padding tests avoid bit3')
        padding_rows.append((h,terms,units))
    require(last == 2009 and hits(last) == [(A,c[0])]
            and not hits(2010) and c[0]+57 < RHO,
            'Complete last product and zero top field reset every cell origin')
    delta = [max(dc)+977,986,977]
    require(delta == [1982,986,977] and all(L-(e+1)>=3 for e in delta)
            and min(min(dc)+977,986,977)>916,
            'All ordinary safe-dummy degrees and padding exclusions')
    require(dc[A] == c[1]+1 and A+977 == 1981,
            'Complete local safe-dummy collision retains both coefficients')

    phase_offsets = sorted({(A-e)%L for e in support
                            if all((h-((A-e)%L))%L in support for h in list(range(961,969))+[A])})
    multiple = [r for r in phase_offsets if r and sum(0<=h-r<942 for h in range(961,969))>=2]
    require(len(phase_offsets)==935 and len(multiple)==932
            and set(phase_offsets)-set(multiple)=={0,19,20}, 'Every whole-field phase is accounted for')
    graphs = module.phase_graphs(tiles)
    universal = module.universal_phase_controls()
    ctl, whole = module.controller(parent,c,support,tiles,spec)
    require(ctl['L']==L==2011 and ctl['d']==D==94517
            and [row['p'] for row in ctl['fixed']]==[47,2011]
            and [row['base2_order']['order'] for row in ctl['fixed']]==[23,402]
            and [row['B_order']['order'] for row in ctl['fixed']]==[23,402]
            and ctl['spacing']==9246 and gcd(D,9246)==1
            and ctl['selected_lambda']==120199>D, 'Entire fixed controller and auxiliary prime')
    require(all(parent.least_factor(p) is None for p in (47,2011,120199,23,2,3,67))
            and [row['base2_order']['prime_factors'] for row in ctl['fixed']]==[[23],[2,3,67]]
            and all(gcd(D,row['B_order']['order'])==1 for row in ctl['fixed'])
            and (120199-1)%9246==0,
            'Every fixed/auxiliary prime, complete proper-order factors and coprime order')
    require([row['H'] for row in ctl['fixed']]==[29,674]
            and ctl['auxiliary_trials'][-1]['H']==36379
            and ctl['auxiliary_trials'][-1]['lift_quotient']==60739
            and ctl['auxiliary_trials'][-1]['lift_residue']==7300767062
            and ctl['auxiliary_trials'][-1]['B_squared']!=1
            and all(row['B_squared']!=1 and row['H']!=0 for row in ctl['fixed']),
            'Whole-K fixed units and exact valuation-one lift')
    power = lambda e:1<<(47*e)
    B,beta=power(L),power(L)-1
    whole_dc=sum(v*power(e) for e,v in dc.items())
    native=8*sum(power(e) for e in range(917))-4+(M-4)*power(CENTER)
    native+=sum(power(e) for e in range(960,969))+sum(power(e) for e in range(987,995))+power(A)
    independently={'beta':beta,'K':whole_dc+B*power(9),
                   'MC':beta-sum(power(e) for e in support),'MF_source':beta+native}
    require(independently==whole and native.bit_count()==978
            and whole['MC'].bit_count()==D-978 and 0<whole_dc<B
            and 0<whole['MC']<beta<whole['MF_source']<2*beta,
            'Independent whole four-port recipe, actual populations and scalar boxes')
    mask_rank=module.actual_mask_rank_checks(whole,spec,L)
    ports={name:{'bits':v.bit_length(),'bytes':(v.bit_length()+7)//8,
                 'sha256':sha(v.to_bytes((v.bit_length()+7)//8,'big'))} for name,v in whole.items()}
    require(sum(row['bytes'] for row in ports.values())==47313,'Whole four-port raw size')
    require((M+2+1+1)&(M-4)==4,
            'Negative C1004: its overlapping marker adds both Start and temporal marker, violating the clause bit2')
    require(sum(c[458:])+1024+60>=RHO,
            'Negative extension: the same unconditional staircase reset bound fails immediately past its endpoint')
    return {'schema':'padding_staircase2011_probe_v1','script_sha256':sha(Path(__file__).read_bytes()),
            'parent_sha256':PARENT_SHA,'source_proof_sha256':module.PROOF_SHA,
            'seed_sha256':sha(seed.encode()),'actions_sha256':sha(encoded(actions)),
            'tiles_sha256':sha(encoded(tiles)),'all3297_coefficients_sha256':sha(encoded(c)),
            'specification':spec,'L':L,'d':D,'raw_bytes':47313,'constant_ports':ports,
            'controller':ctl,'whole_field_graphs':graphs,'uniform_graph_controls':universal,
            'low_conditional_geometry':{'count':len(low_rows),'sha256':sha(encoded(low_rows)),
                                       'maximum':max(row[2] for row in low_rows)},
            'early_unconditional_geometry':{'count':len(early_rows),'sha256':sha(encoded(early_rows))},
            'prefix_staircase':{'first':first,'last':endpoint,'count':483,
                               'sha256':sha(encoded(stair_rows)),'phase_controls':stair_controls},
            'all47_fractional_phases':phase_rows,
            'copy_geometry':{'count':len(copy_rows),'sha256':sha(encoded(copy_rows))},
            'padding_geometry':{'count':len(padding_rows),'sha256':sha(encoded(padding_rows)),
                                'maximum_selector_source':896},
            'clause_source':1,'predecessor_extra_sources':['selector0','temporal_marker'],
            'marker_collision_coefficient':dc[A],'adjacency_bound':adj_bound,
            'whole_boolean_convolution':{'count':len(envelope),'maximum':max(envelope),'sha256':sha(encoded(envelope))},
            'whole_field_phases':{'count':len(phase_offsets),'sha256':sha(encoded(phase_offsets))},
            'delta_exponents':delta,'actual_mask_rank_checks':mask_rank,
            'negative_controls':{'C1004_Start_clause_bit2':4,'staircase_endpoint_plus_one_tail':sum(c[458:])},
            'scope':'Full finite geometry/controller exploration with a separate ordinary dependency note; no native proof promotion, no equation-size minimum, no incoming execution.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    data=run()
    raw=encoded(data)
    if args.write:
        (HERE/'RESULTS.json').write_bytes(raw)
    else:
        require((HERE/'RESULTS.json').read_bytes()==raw,'Exact deterministic complete receipt')
    print(json.dumps({'status':'PASS','L':L,'raw_bytes':data['raw_bytes'],
                      'script_sha256':data['script_sha256'],'receipt_sha256':sha(raw)},sort_keys=True))


if __name__=='__main__':
    main()
