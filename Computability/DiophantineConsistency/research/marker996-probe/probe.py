#!/usr/bin/env python3
"""Isolated complete finite exploration of marker996/clause995/length1997."""
import argparse
import hashlib
import importlib.util
import json
from math import gcd, lcm, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'padding-staircase-independent/certify.py'
PARENT_SHA = '56b3865237699c486bbd940a88e94387d26092ac2cf89cd7f9097206dd8fb975'
RHO, M, A, CENTER, L = 1 << 47, 1 << 45, 996, 995, 1997
D = 47 * L
SPEC = {'south':942,'west':969,'north':960,'east':978,'dummy':977,
        'anchor':A,'temporal':18,'west_copy':18,'spatial':9,
        'centers':[CENTER],'padding':1,'padding_last':916,'zero_tail':1993}


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2, sort_keys=True) + '\n').encode()


def source():
    require(sha(PARENT.read_bytes()) == PARENT_SHA, 'Exact reviewed complete2011 parent before import')
    spec = importlib.util.spec_from_file_location('frozen_staircase2011', PARENT)
    require(spec is not None and spec.loader is not None, 'Authenticated module loader')
    old = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(old)
    module, parent, seed, actions, tiles, c, support = old.source()
    require(support == set(range(951)) | set(range(960,986)) | {1004}, 'Entire old physical support')
    return old, module, parent, seed, actions, tiles, c, support - {1004} | {A}


def compressed(rows):
    return {'count':len(rows), 'sha256':sha(encoded(rows))}


def controller(module, parent, c, support, tiles, minimum):
    trials = []
    for length in range(minimum, minimum + 101):
        primes = parent.factors(length)
        row = {'L':length, 'prime_factors':primes}
        trials.append(row)
        if length % 2 == 0 or 47 in primes or prod(primes) != length:
            row['rejection'] = 'Odd squarefree length coprime to47 required'
            continue
        whole = module.whole_constants(c, support, SPEC, length)
        fixed = []
        for p in [47] + primes:
            require(parent.least_factor(p) is None, 'Every fixed factor is prime')
            item = module.modular(p, c, tiles, SPEC, length, whole)
            item['base2_order'] = parent.order(2,p)
            item['B_order'] = parent.order(item['B'],p)
            fixed.append(item)
        row['fixed'] = fixed
        d = 47 * length
        if any(item['H']==0 or item['B_squared']==1 or gcd(d,item['B_order']['order'])!=1 for item in fixed):
            row['rejection'] = 'Fixed controller unit/order condition fails'
            continue
        spacing = lcm(*(item['B_order']['order'] for item in fixed))
        require(gcd(d,spacing)==1, 'Whole spacing coprime to all of d')
        auxiliary=[]
        for multiplier in range((d-1)//spacing+1,(d-1)//spacing+502):
            p=spacing*multiplier+1
            item={'candidate':p,'multiplier':multiplier,'least_factor':parent.least_factor(p)}
            auxiliary.append(item)
            if item['least_factor'] is not None:
                continue
            item.update(module.modular(p,c,tiles,SPEC,length,whole))
            lift=pow(2,d*(p-1),p*p)
            require(lift%p==1,'Exact Fermat lift')
            item.update({'lift_residue':lift,'lift_quotient':(lift-1)//p})
            if item['H'] and item['B_squared']!=1 and item['lift_quotient']:
                require(p>d and p%2==1,'Odd auxiliary prime above d')
                return {'L':length,'d':d,'length_trials':trials,'fixed':fixed,'spacing':spacing,
                        'auxiliary_trials':auxiliary,'selected_lambda':p},whole
        row['rejection']='No successful auxiliary prime in501 progression terms'
    raise ValueError('No complete controller found in101 tested lengths')


def run():
    old,module,parent,seed,actions,tiles,c,support=source()
    require(len(c)==3297 and max(c)<M and all(v%2==0 for v in c)
            and sum(c[942:])==M-2048 and c[A]==0, 'Whole unchanged doubled coefficient array')
    require(len(support)==978 and support==set(range(951))|set(range(960,986))|{A},
            'Whole relocated zero-weight physical marker')
    dc=module.dc_coefficients(c,SPEC)
    expected={CENTER-e:v for e,v in enumerate(c) if v}
    for e in (18,A):
        expected[e]=expected.get(e,0)+1
    require(dc==expected and min(dc)==10 and dc[A]==1 and dc[18]==1,
            'All reflected coefficients plus both bare units, with no unhandled collision')

    def hits(h):
        return [(e,dc[h-e]) for e in sorted(support) if h-e in dc]

    def parity(h):
        return [(e,v%2) for e,v in hits(h) if v%2]

    def reflected(h):
        return [(e,CENTER+e-h,c[CENTER+e-h]) for e in sorted(support)
                if 0<=CENTER+e-h<len(c) and c[CENTER+e-h]]

    last=max(dc)+max(support)
    require(last==2*A==1992 and hits(1992)==[(A,1)]
            and hits(1991)==[(A,c[0])] and not hits(1993),
            'Actual tail is controlled by the bare marker squared, with its following zero')
    envelope=[sum(v for _,v in hits(h)) for h in range(last+1)]
    require(max(envelope)+1+RHO//2+57<58*RHO,'Whole cyclic raw envelope permits carry57')
    low=[]
    for h in range(A):
        terms=reflected(h)
        select=[v for e,_,v in terms if e<942]
        controls=[(index,v) for e,index,v in terms if e>=942]
        require(all(index>=942 for index,_ in controls) and sum(v for _,v in controls)<=M-2048,
                'Every conditional control-source coefficient lies among the entire label family')
        bound=max(select,default=0)+sum(v for _,v in controls)
        require(bound+3+RHO//2+57<RHO,'Every field through995 resets under one-hot before label decoding')
        low.append([h,terms,bound])
    first,end=CENTER-941,CENTER-459
    require((first,end)==(54,536) and end-first+1==483,'Complete shifted padding staircase')
    early,stairs=[],[]
    for h in range(end+1):
        terms=reflected(h)
        require(all(index>=459 for _,index,_ in terms) and sum(v for _,_,v in terms)<=sum(c[459:])
                and sum(v for _,_,v in terms)+3+1024+57<RHO,'Unconditional early reset including predecessor53')
        early.append([h,terms])
        if h>=first:
            prefix=[e for e,index,v in terms if index<942]
            require(prefix==list(range(h-first+1)) and all(v%2048==(2 if index<942 else 0) for _,index,v in terms)
                    and h<A,'Each successive actual padding test exposes exactly one more selector')
            stairs.append([h,prefix])
    stair_cases=[]
    for phase in range(7,11):
        reachable={0}
        for _ in range(483):
            reachable={n+bit for n in reachable for bit in (0,1) for units in range(3) for t in (0,1)
                       if ((2*(n+bit)+units+(t<<phase))%RHO)&8==0}
            require(reachable<={0,1,2,3},'First prefix count4 is excluded at every step')
        require(reachable=={0,1,2,3},'Exact complete prefix count bound')
        stair_cases.append([phase,sorted(reachable)])
    count_cases=[]
    for phase in range(47):
        upper=462 if 7<=phase<=10 else 942
        survivors=[(n,k,dummy,t) for n in range(upper+1) for k in range(58) for dummy in (0,1) for t in (0,1)
                   if ((2*n+k+dummy+(t<<phase))%RHO)&2044==0]
        require(survivors and max(row[0] for row in survivors)==1,'Every phase recovers preliminary one-hot')
        require((2*upper+57+1+(1<<phase)<2048) if phase<=10 else ((1<<phase)%2048==0),
                'All count ranges justify the actual low-bit reduction')
        count_cases.append({'phase':phase,'n_bound':upper,**compressed(survivors)})

    copy=[]
    for j in range(9):
        h=960+j
        require(parity(h)==[(942+j,1)] and h-9 not in support,'Complete South copy odd part')
        copy.append([h,hits(h),None])
    for j in range(8):
        h=987+j
        require(parity(h)==[(969+j,1)] and h-9==978+j and h not in support,'Complete spatial copy odd part')
        copy.append([h,hits(h),h-9])
    require(parity(A)==[(0,1),(978,1)] and A-9 not in support,'Marker odd part is Start plus current Eastbit0')
    start=(255-tiles[0][0],511-tiles[0][1],255-tiles[0][2],511-tiles[0][3])
    packed=start[0]+(start[1]<<8)+(start[2]<<17)+(start[3]<<25)
    require(start==(253,76,252,510) and start[2]%2==0,'Complete Start calibration including marker extra0')
    local=[]
    for phase in range(47):
        accepted=[]
        for k in range(58):
            for dummy in (0,1):
                for t in (0,1):
                    for residue in range(4):
                        numerator=(residue-c[0]-k-dummy-(t<<phase))%M
                        if numerator%2048:
                            continue
                        word=numerator//2048
                        require(((c[0]+2048*word+k+dummy+(t<<phase))%RHO)&(M-4)==0,
                                'Actual origin mask accepts every enumerated label')
                        require(word>>25!=0,'Every accepted Start local mask has nonzero South before labels')
                        accepted.append([k,dummy,t,residue,word])
        require(accepted,'Complete origin enumeration nonempty before copy tests')
        if phase:
            require(all((t<<phase)%2==0 for t in (0,1)),'Positive binary phases force all reset South-copy bits0')
        local.append({'phase':phase,**compressed(accepted),'south_values':sorted({r[-1]>>25 for r in accepted})})

    clause={e:c[e] for e in support if c[e]}
    clause[977]=clause.get(977,0)+1
    adjacent={e:c[e+1] for e in support if c[e+1]}
    adjacent[976]=adjacent.get(976,0)+1
    require(hits(CENTER)==sorted(clause.items()) and CENTER not in support and CENTER-9 not in support,
            'Whole clause is reflected coefficients plus only the Boolean dummy')
    require(hits(CENTER-1)==sorted(adjacent.items()) and CENTER-1==994
            and 994-9==985 and 994 not in support,'Whole predecessor is adjacency plus West7 and spatial East7')
    adjbound=max((c[e+1] for e in support if e<942),default=0)+sum(c[e+1] for e in support if e>=942)
    require(adjbound+2+57<RHO and all((M+2+dummy)&(M-4)==0 for dummy in (0,1)),
            'Complete aligned predecessor reset and both canonical clause increments')
    padding=[]
    for h in range(1,917):
        terms=reflected(h)
        require(all(e<=906 and e<942 and v%2048 in (0,2) for e,_,v in terms),'Every padding reflection is selector-sourced')
        units=int(h-18 in support)+int(h-9 in support)+int(h in support)
        require(max((v%2048 for _,_,v in terms),default=0)+units<=5,'Every canonical padding digit avoids bit3')
        padding.append([h,terms,units])
    phases=sorted({A-e for e in support if all(h-(A-e) in support for h in list(range(961,969))+[A])})
    multiple=[r for r in phases if r and sum(0<=h-r<942 for h in range(961,969))>=2]
    require(len(phases)==936 and len(multiple)==932 and set(phases)-set(multiple)=={0,18,19,20},
            'Every complete whole-field offset is classified')
    # For offset18, E0(theta)=E0(current) xor Start(current). A Start
    # state has E0=0, so this Boolean value can only increase around cycles.
    transitions=[['empty',0,0,0]]
    for j,tile in enumerate(tiles):
        bit=(255-tile[2])%2
        flag=int(j==0)
        nxt=bit^flag
        require(nxt>=bit and (not flag or (bit,nxt)==(0,1)),'Complete decoded offset18 transition is monotone, strict at Start')
        require(flag+bit<=1,'Canonical marker is Boolean Start+East0 on every decoded tile')
        transitions.append([j,flag,bit,nxt])
    require([h-18 for h in range(960,969)]==list(range(942,951)) and A-18==978,
            'Exact offset18 sources for all South copies and marker')
    graphs=module.phase_graphs(tiles)
    delta=[max(dc)+977,986,977]
    require(delta==[1973,986,977] and all(L-(e+1)>=3 for e in delta)
            and min(min(dc)+977,986,977)>916,'Complete arbitrary dummy increment margins')
    require(last+2==1994,'Controller search starts after an actual zero top field, not center+anchor alone')
    ctl,whole=controller(module,parent,c,support,tiles,last+2)
    require(ctl['L']==L and ctl['d']==D and ctl['selected_lambda']>D,'Entire selected controller')
    require(L>last+1 and not any(hits(h) for h in range(last+1,L)),'All actual top zero fields')
    raw=sum((v.bit_length()+7)//8 for v in whole.values())
    ports={name:{'bits':v.bit_length(),'bytes':(v.bit_length()+7)//8,
                 'sha256':sha(v.to_bytes((v.bit_length()+7)//8,'big'))} for name,v in whole.items()}
    # The original C997 proposal has a concrete admissible-tile obstruction.
    require(tuple(tiles[1])==(0,433,0,438) and ((255-tiles[1][2])>>1)&1==1
            and (M+2+1+1)&(M-4)==4,'Actual sorted tile1 rejects the former C997 canonical clause')
    return {'schema':'marker996_clause995_probe_v1','script_sha256':sha(Path(__file__).read_bytes()),
            'parent_sha256':PARENT_SHA,'parent_proof_sha256':old.PROOF_SHA,
            'specification':SPEC,'L':L,'d':D,'raw_bytes':raw,'constant_ports':ports,
            'all3297_coefficients_sha256':sha(encoded(c)),'all942_tiles_sha256':sha(encoded(tiles)),
            'whole_boolean_convolution':{**compressed(envelope),'maximum':max(envelope)},
            'conditional_reset':{**compressed(low),'maximum':max(row[2] for row in low)},
            'early_reset':compressed(early),'staircase':{'first':first,'last':end,**compressed(stairs),'cases':stair_cases},
            'all47_count_cases':count_cases,'all47_origin_mask_cases':local,
            'copy_geometry':compressed(copy),'padding_geometry':compressed(padding),
            'whole_field_offsets':{**compressed(phases),'exceptions':[0,18,19,20],'multiple_selectors':len(multiple)},
            'offset18_transitions':{**compressed(transitions),'Start_edge':[0,1],'monotone':True},
            'offset19_20_graphs':graphs,'adjacency_bound':adjbound,'delta_exponents':delta,
            'controller':ctl,'actual_mask_rank_checks':module.actual_mask_rank_checks(whole,SPEC,L),
            'canonical_C997_negative':{'tile1':list(tiles[1]),'complemented_East':255,'violated_bit':2},
            'scope':'Complete finite exploration only; prospective full ordinary native proof and peer review remain required. No minimum or formal-kernel replay claim.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result=run()
    raw=encoded(result)
    path=HERE/'RESULTS.json'
    if args.write:
        path.write_bytes(raw)
    else:
        require(path.read_bytes()==raw,'Exact deterministic finite exploration receipt')
    print(json.dumps({'status':'PASS','L':result['L'],'raw_bytes':result['raw_bytes'],
                      'script_sha256':result['script_sha256'],'receipt_sha256':sha(raw)},sort_keys=True))


if __name__=='__main__':
    main()
