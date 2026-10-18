#!/usr/bin/env python3
"""Phase-aware affine register vectors and exact appended-zero spare tails.

Each primary value is an exact constant or initial physical variable plus an
integer offset. A decrement is used only when zero or positivity follows
from the initial phase/guard bounds. Positive decrement appends one zero
spare; the appended count is tracked throughout. At dispatcher comparison,
the accepted relation permits any valid spare suffix (or --exact-spares
requires the original operation's exact appended count).

This composes only the original unchanged four Box contracts. It admits
multiple register excursions whose net primary-register effect is correct.
It is a bounded Python diagnostic, not a Lean-verified symbolic executor.
"""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,json,time,hashlib
import rotation_search252 as r
import check_rotation252 as c
from fold_changed252 import read_table

INITIAL=()
BOUNDS=()
EXACT_SPARES=False
OPS=Counter()
LAST_SPARES=0
OLD_CANON=c.strict.canon

def plus(expr,k):return (expr[0],expr[1]+k)

def vector(state):
    if state[0]=='V':return state[1],state[2]
    assert state[0]=='plain'
    vs=list(INITIAL);spares=0
    if state[1] is not None:
        kind,index=state[1];vs[index]=plus(vs[index],1 if kind=='inc' else -1);spares=int(kind=='dec')
    return tuple(vs),spares

def lower_upper(expr):
    v,k=expr
    if v==-1:return k,k
    lo,hi=BOUNDS[v]
    return lo+k,None if hi is None else hi+k

def oracle(q,branch,state):
    if state[0] in ('plain','V') and q in c.strict.SKIP:
        vs,tail=vector(state);index=c.strict.SKIP[q];OPS['mark']+=1
        return ('2' if index==0 else '6'),('M',index,vs,tail)
    if state[0]=='M':
        _,index,vs,tail=state
        if q=='73':
            new=list(vs);new[index]=plus(new[index],1);OPS['inc']+=1
            return '48',('V',tuple(new),tail)
        if q=='43':
            lo,hi=lower_upper(vs[index]);assert lo>=0
            if hi==0:
                OPS['dec_zero']+=1
                return '3',('V',vs,tail)
            if lo>=1:
                new=list(vs);new[index]=plus(new[index],-1);OPS['dec_positive']+=1
                return ('63' if index==0 else '48'),('V',tuple(new),tail+1)
            OPS['unknown_guard']+=1
    return None

def project_state(state):
    global LAST_SPARES
    if state[0] in ('plain','V'):
        vs,tail=vector(state);LAST_SPARES=tail
        return ('vec_exact',vs,tail) if EXACT_SPARES else ('vec_valid_spares',vs)
    return state

def project_canonical(pair):
    return tuple(tuple(('box',project_state(seg[1])) if seg[0]=='box' else seg for seg in side) for side in pair)

def canon(left,right):return project_canonical(OLD_CANON(left,right))

def establish_domain(mask,operation,arg,zero):
    global INITIAL,BOUNDS
    logical=list(mask)
    if operation=='CD':logical[arg]&=1 if zero else 6
    assert all(logical)
    initial=[None]*9;bounds=[None]*9
    for logical_index,physical in enumerate(r.NEWPHYS):
        m=logical[logical_index]
        lo=0 if m&1 else 1 if m&2 else 2
        hi=None if m&4 else 1 if m&2 else 0
        initial[physical]=(-1,lo) if lo==hi else (physical,0)
        bounds[physical]=(lo,hi)
    INITIAL=tuple(initial);BOUNDS=tuple(bounds)

def main():
    global INITIAL,BOUNDS,OPS,LAST_SPARES,EXACT_SPARES
    ap=argparse.ArgumentParser();ap.add_argument('--exact-spares',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args();EXACT_SPARES=args.exact_spares
    r.NEWPHYS=(4,5,0,8,6,2,1,7,3);folder=r.HERE/'rotation-candidates';d=json.loads((folder/'mp-cache-permuted252.json').read_text());nodes={int(k):tuple(map(tuple,v)) for k,v in d['nodes'].items()};root=d['root'];table=read_table(folder/'mp-cache-permuted252.tm');phase=json.loads((r.HERE/'mp-cache-safe-phase.json').read_text());allcases=list(c.cases(nodes,root));excluded={x['case'] for x in phase['excluded']};cases=[i for i in range(len(allcases)) if i not in excluded]
    c.strict.oracle=oracle;c.strict.canon=canon
    states=sorted({q for q,b in table},key=int);protected={(str(q),b) for q,b in c.audit.BOX_PAIRS};protected_targets={table[k][2] for k in protected};eligible=[q for q in states if q!='96' and q not in protected_targets and all((q,b)not in protected for b in (0,1))]
    def check(current,i):
        global OPS,LAST_SPARES
        p,op,arg,z,branch,target=allcases[i];establish_domain(phase['masks'][p],op,arg,z);actualtarget=project_canonical(target);OPS=Counter();LAST_SPARES=0
        try:
            rules,literal=c.strict.run(current,p,branch,actualtarget,halt=op=='CH',fuel=1000);assert literal>0
            return sum(rules.values()),None,dict(OPS),LAST_SPARES
        except (AssertionError,KeyError) as ex:return 0,str(ex),dict(OPS),LAST_SPARES
    # A genuine inverse pair restores the exact vector and appends one spare.
    establish_domain([1]*9,'CI',0,None);start=('plain',None);q,marked=oracle('60',None,start);q,inc=oracle('73',None,marked);q,marked=oracle('60',None,inc);q,dec=oracle('43',None,marked)
    assert dec==('V',INITIAL,1)
    # Without a lower bound an unknown input decrement must not be used.
    establish_domain([7]*9,'CC',0,None);q,marked=oracle('60',None,('plain',None));assert oracle('43',None,marked) is None
    usage=defaultdict(list);first=time.monotonic();baseline_spares=Counter()
    for i in cases:
        t=c.Tracking(table);cost,why,ops,spares=check(t,i);assert why is None,(i,why);baseline_spares[spares]+=1
        for q in {q for q,b in t.used}:usage[q].append((cost,i))
    for group in usage.values():group.sort()
    print('BASELINE',len(cases),'spares',dict(baseline_spares),'eligible',len(eligible),'exact',EXACT_SPARES,flush=True)
    ledger=[];survivors=[];checks=0;multi_attempts=0;reasoncounts=Counter();accepted_multi={}
    for k,dead in enumerate(eligible):
        record={'deleted':int(dead),'failures':[]}
        for target in states:
            if target==dead:continue
            changed={(q,b):(w,d,target if t==dead else t) for(q,b),(w,d,t)in table.items() if q!=dead};assert all(changed[x]==table[x] for x in protected)
            failed=None;why=None;cert={}
            for _,i in usage[dead]:
                _,why,ops,tail=check(changed,i);checks+=1;multi_attempts+=int(ops.get('mark',0)>1)
                if why is not None:failed=i;break
                if ops.get('mark',0)>1:cert[i]={'operations':ops,'appended_zero_spares':tail};accepted_multi.setdefault(str(i),{'dead':dead,'target':target,**cert[i]})
            if failed is None:
                cert={}
                for i in cases:
                    _,why,ops,tail=check(changed,i);checks+=1;multi_attempts+=int(ops.get('mark',0)>1)
                    if why is not None:failed=i;break
                    if ops.get('mark',0)>1:cert[i]={'operations':ops,'appended_zero_spares':tail};accepted_multi.setdefault(str(i),{'dead':dead,'target':target,**cert[i]})
            if failed is None:
                stem=f'vector-{"exact" if EXACT_SPARES else "spare"}-delete{dead}-to{target}-251';output=folder/(stem+'.tm');r.save(output,changed);output.write_text(output.read_text().replace('#! start 64\n','#! start 0\n',1));certificate={'deleted':int(dead),'target':int(target),'table':stem+'.tm','cases':len(cases),'multiple_excursion_cases':cert,'table_sha256':hashlib.sha256(output.read_bytes()).hexdigest()};survivors.append(certificate);print('SURVIVOR',json.dumps(certificate),flush=True)
            else:reasoncounts[why]+=1
            record['failures'].append([int(target),failed])
        ledger.append(record)
        if k%25==0:print('Progress',k+1,'checks',checks,'multi',multi_attempts,'survivors',len(survivors),'elapsed',round(time.monotonic()-first,2),flush=True)
    result={'source_table':'mp-cache-permuted252.tm','source_sha256':hashlib.sha256((folder/'mp-cache-permuted252.tm').read_bytes()).hexdigest(),'logical_to_physical':r.NEWPHYS,'initial_logical_registers':phase['initial_registers'],'phase_invariant_file':'mp-cache-safe-phase.json','phase_cases':len(cases),'excluded_case_numbers':sorted(excluded),'exact_spares_required':EXACT_SPARES,'recipes':len(eligible)*(len(states)-1),'checks':checks,'checks_with_multiple_marks':multi_attempts,'accepted_multiple_excursion_cases':accepted_multi,'survivors':survivors,'elapsed_seconds':time.monotonic()-first,'reason_counts':reasoncounts,'ledger':ledger,'scope':'Exact symbolic primary-register vectors with proved zero/positive guards. Each positive decrement appends one explicit zero spare. Dispatcher equality projects only spare tail when exact_spares_required=false; its validity follows by closure of finite unary-block suffixes. Python checker not kernel verified; candidate bootstrap separate.'}
    output=args.output or r.HERE/f'vector-effect-{"exact" if EXACT_SPARES else "spare"}-fold-results.json';output.write_text(json.dumps(result,indent=2)+'\n');print('DONE',result['recipes'],checks,'survivors',len(survivors),'multichecks',multi_attempts,'elapsed',result['elapsed_seconds'],flush=True)

if __name__=='__main__':main()
