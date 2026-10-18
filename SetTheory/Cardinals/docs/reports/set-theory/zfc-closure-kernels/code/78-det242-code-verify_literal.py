#!/usr/bin/env python3
"""Complete finite literal regression for Detour242's 8,390 source/guard cases.

Adapted from reference/rotation244/check_qt244_literal.py, inherited from the
QT loop-rotation contribution in ProveIt. The original deterministic fixtures,
physical register permutation and expected source-frame construction are
retained. This adaptation binds the exact Detour242 table, requires all 484
rows to be exercised, and checks the complete halting configuration against
Combined243 for the sole CH fixture. All other cases compare whole tapes to
independently constructed expected source frames.

Only Python's standard library is used. These finite fixtures supplement the
unbounded ordinary proof; they do not themselves establish consistency or an
unbounded simulation theorem. No reference input is modified.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse
import gzip
import json
import time

ROOT=Path(__file__).resolve().parents[1]
TABLE_SHA='c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
BASELINE_SHA='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
SITES_SHA='3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
PHYSICAL=(6,2,0,4,3,7,8,5,1)


def read_table(path,states_expected):
    table={};start=None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):
            assert start is None
            start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in table
        table[q,b]=(w,1 if d=='R'else-1,t)
    assert start==95
    states={q for q,b in table}
    assert len(states)==states_expected and len(table)==2*states_expected
    assert set(table)=={(q,b)for q in states for b in(0,1)}
    assert {q for w,d,q in table.values()}-states=={254}
    return table


def increment(path):
    bits=list(path)
    for i in range(len(bits)-1,-1,-1):
        if bits[i]=='0':
            bits[i]='1';return ''.join(bits),False
        bits[i]='0'
    return ''.join(bits),True


def strip(path,bit,count):
    while count and path:
        count-=int(path[-1]==bit);path=path[:-1]
    return path


def frame(head,path,span,logical,spares):
    assert span>=len(path) and len(logical)==9 and spares
    assert set(PHYSICAL)==set(range(9))
    ones={head-1,head+span}
    ones.update(head+i for i,b in enumerate(path)if b=='1')
    physical=[None]*9
    for i,j in enumerate(PHYSICAL):physical[j]=logical[i]
    pos=head+span+1
    for value in physical+spares:
        assert type(value)is int and value>=0
        ones.update(range(pos+1,pos+value+2));pos+=value+2
    return ones


def baseline_halt(table,initial,limit):
    ones=set(initial);q,head=96,0
    for steps in range(1,limit+1):
        key=q,int(head in ones)
        assert key in table,('unexpected baseline halt',q,head)
        write,direction,q=table[key]
        if write:ones.add(head)
        else:ones.discard(head)
        head+=direction
        if q==254:return q,head,ones,steps
    raise AssertionError('Baseline CH fixture exceeded the literal step limit')


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table',type=Path,default=ROOT/'machine/zfc_detour242_old.tm')
    parser.add_argument('--sites',type=Path,default=ROOT/'machine/sites_logical.json')
    parser.add_argument('--baseline',type=Path,default=ROOT/'reference/zfc_combined243_old.tm')
    parser.add_argument('--output',type=Path,default=ROOT/'evidence/literal-runtime.json')
    parser.add_argument('--cases-output',type=Path,default=ROOT/'evidence/literal-runtime-cases.json.gz')
    parser.add_argument('--step-limit',type=int,default=20000)
    a=parser.parse_args();assert a.step_limit>0
    paths={'table':a.table,'source':a.sites,'baseline_CH_reference':a.baseline,
           'checker':Path(__file__).resolve()}
    before={key:sha256(path.read_bytes()).hexdigest()for key,path in paths.items()}
    assert before['table']==TABLE_SHA
    assert before['source']==SITES_SHA
    assert before['baseline_CH_reference']==BASELINE_SHA
    table=read_table(a.table,242);baseline=read_table(a.baseline,243)
    sites=json.loads(a.sites.read_text());assert len(sites)==6459
    assert sum(2 if op=='CD'else 1 for pc,op,r in sites)==8390
    assert sum(op=='CH'for pc,op,r in sites)==1
    used=Counter();records=[];began=time.monotonic();total=0
    halt_controls=[];frame_comparisons=0
    for index,(pc,op,r)in enumerate(sites):
        assert isinstance(pc,str)and set(pc)<=set('01')
        assert op in('CI','CD','CB','CC','CH')
        if op=='CH':assert r is None
        else:assert type(r)is int and r>=0
        if op in('CI','CD'):assert r<9
        for zero in((True,False)if op=='CD'else(None,)):
            serial=len(records)
            # Fresh deterministic values are not filtered by source
            # reachability; even scratch registers may be nonzero.
            logical=[(17*serial+11*j+3*index+7)%23 for j in range(9)]
            if op=='CD':logical[r]=0 if zero else 1+(13*serial+7*r)%23
            spares=[(serial+2*j+3)%13 for j in range(1+serial%5)]
            span=64+17*(serial%3)
            ones=frame(0,pc,span,logical,spares)
            output=logical.copy();tail=spares.copy();extra=0;overflow=False
            if op=='CI':output[r]+=1;tail.append(1);successor,overflow=increment(pc)
            elif op=='CD'and not zero:output[r]-=1;extra=1;successor,overflow=increment(pc)
            elif op=='CD':successor,overflow=increment(strip(pc,'0',1))
            elif op=='CB':successor,overflow=increment(strip(pc,'0',r))
            elif op=='CC':successor=strip(pc,'1',r)
            else:successor=''
            endhead=-int(overflow)
            if op=='CH':
                expected_q,endhead,expected,baseline_steps=baseline_halt(baseline,ones,a.step_limit)
            else:
                expected_q=96
                expected=frame(endhead,successor,span+extra+int(overflow),output,tail)
            q,head=96,0
            for steps in range(1,a.step_limit+1):
                key=q,int(head in ones)
                assert key in table,('unexpected halt',serial,index,pc,op,r,zero,q,head)
                write,direction,q=table[key];used[key]+=1
                if write:ones.add(head)
                else:ones.discard(head)
                head+=direction
                if op=='CH'and q==254:
                    assert (q,head,ones)==(expected_q,endhead,expected),('CH whole-configuration mismatch',serial,index,head,endhead)
                    halt_controls.append({'serial':serial,'index':index,'baseline_steps':baseline_steps,
                        'candidate_steps':steps,'final_state':q,'final_head':head,
                        'one_cells':len(ones),'entire_tape_equal':True})
                    break
                if op!='CH'and q==96 and head==endhead and ones==expected:
                    frame_comparisons+=1;break
            else:raise AssertionError(('literal step limit',serial,index,pc,op,r,zero,q,head))
            assert (q,head,ones)==(expected_q,endhead,expected)
            total+=steps
            records.append({'index':index,'pc':pc,'op':op,'r':r,'zero':zero,
                'logical_registers':logical,'spare_values':spares,'initial_span':span,
                'steps':steps,'final_head':head,'final_state':q,
                'whole_tape_endpoint_equal':True})
        if index%1000==0:print('literal sites',index,'cases',len(records),flush=True)
    assert len(records)==8390 and frame_comparisons==8389 and len(halt_controls)==1
    assert set(used)==set(table),('uncovered or extra literal rows',set(table)-set(used),set(used)-set(table))
    assert len(used)==484 and sum(used.values())==total
    after={key:sha256(path.read_bytes()).hexdigest()for key,path in paths.items()}
    assert before==after,('Input changed during verification',before,after)
    out={'status':'PASS_COMPLETE_FINITE_LITERAL_RUNTIME','complete_source_case_coverage':True,
        'cases':len(records),'source_leaves':len(sites),'working_states':242,'binary_rows':484,
        'table_sha256':TABLE_SHA,'source_sha256':SITES_SHA,'literal_steps':total,
        'minimum_case_steps':min(x['steps']for x in records),'maximum_case_steps':max(x['steps']for x in records),
        'covered_rows':len(used),'all_rows_covered':True,'unused_runtime_rows':[],
        'whole_tape_endpoints_checked':True,'whole_tape_endpoint_cases':len(records),
        'independent_expected_source_frames':frame_comparisons,
        'baseline_expected_halt_configurations':halt_controls,
        'primary_registers_vary_without_source_invariant_filter':True,
        'gap_values':[64,81,98],'nonempty_spare_lengths':[1,2,3,4,5],
        'literal_step_limit_per_case':a.step_limit,'seconds':time.monotonic()-began,
        'inputs_before':before,'inputs_after':after,
        'adapted_from':'reference/rotation244/check_qt244_literal.py (QT loop-rotation contribution)',
        'scope':'Finite deterministic fixtures only; 8389 source-frame comparisons and one exact Combined243-to-Detour242 halt-configuration comparison. Supplements the ordinary unbounded proof.',
        'row_counts':[[q,b,n]for(q,b),n in sorted(used.items())]}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    a.cases_output.parent.mkdir(parents=True,exist_ok=True)
    with gzip.GzipFile(filename=str(a.cases_output),mode='wb',mtime=0)as stream:
        stream.write((json.dumps(records,indent=2)+'\n').encode('ascii'))
    print(json.dumps({k:v for k,v in out.items()if k!='row_counts'},indent=2),flush=True)

if __name__=='__main__':main()
