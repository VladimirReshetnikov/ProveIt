#!/usr/bin/env python3
"""Independent finite literal regression for every QT244 source/guard case.

Only the Python standard library is used. Values are fresh deterministic
fixtures and are not filtered by source reachability. This is a finite
regression, separate from the universal symbolic proof.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse,json,time,gzip

TABLE_SHA='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
SITES_SHA='3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
PHYSICAL=(6,2,0,4,3,7,8,5,1)

def read_table(path):
    table={};start=None
    for line in path.read_text(encoding='ascii').splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in table
        table[q,b]=(w,1 if d=='R'else-1,t)
    assert start==95
    states={q for q,b in table}
    assert len(states)==243 and len(table)==486
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
    assert span>=len(path)
    ones={head-1,head+span}
    ones.update(head+i for i,b in enumerate(path)if b=='1')
    physical=[None]*9
    for i,j in enumerate(PHYSICAL):physical[j]=logical[i]
    pos=head+span+1
    for value in physical+spares:
        assert type(value)is int and value>=0
        ones.update(range(pos+1,pos+value+2));pos+=value+2
    return ones

def main():
    if not __debug__:
        raise RuntimeError('Assertions are required; do not use Python -O.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate',type=Path,required=True)
    parser.add_argument('--step-limit',type=int,default=20000)
    a=parser.parse_args();assert __debug__
    tp=a.candidate/'machine_old.tm';sp=a.candidate/'sites_logical.json'
    assert sha256(tp.read_bytes()).hexdigest()==TABLE_SHA
    assert sha256(sp.read_bytes()).hexdigest()==SITES_SHA
    table=read_table(tp);sites=json.loads(sp.read_text());assert len(sites)==6459
    used=Counter();records=[];began=time.monotonic();total=0
    for index,(pc,op,r)in enumerate(sites):
        for zero in((True,False)if op=='CD'else(None,)):
            serial=len(records)
            # Independent fresh fixture coordinates. Every non-guard register
            # is allowed to be nonzero, including scratch registers.
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
            else:assert op=='CH';successor=''
            endhead=-int(overflow)
            expected=None if op=='CH'else frame(endhead,successor,span+extra+int(overflow),output,tail)
            q,head=96,0
            for steps in range(1,a.step_limit+1):
                key=q,int(head in ones)
                assert key in table,('unexpected halt',serial,index,pc,op,r,zero,q,head)
                write,direction,q=table[key];used[key]+=1
                if write:ones.add(head)
                else:ones.discard(head)
                head+=direction
                if op=='CH'and q==254:break
                if op!='CH'and q==96 and head==endhead and ones==expected:break
            else:raise AssertionError(('literal step limit',serial,index,pc,op,r,zero,q,head))
            total+=steps
            records.append({'index':index,'pc':pc,'op':op,'r':r,'zero':zero,
                'logical_registers':logical,'spare_values':spares,'initial_span':span,
                'steps':steps,'final_head':head,'final_state':q})
        if index%1000==0:print('literal sites',index,'cases',len(records),flush=True)
    assert len(records)==8390
    assert set(table)-set(used)=={(27,1)},('unexpected unused literal rows',set(table)-set(used))
    out={'status':'PASS_FINITE_LITERAL_REGRESSION','complete_source_case_coverage':True,
        'cases':len(records),'source_leaves':len(sites),'working_states':243,
        'table_sha256':TABLE_SHA,'source_sha256':SITES_SHA,'literal_steps':total,
        'minimum_case_steps':min(x['steps']for x in records),'maximum_case_steps':max(x['steps']for x in records),
        'covered_rows':len(used),'all_rows_covered':False,'unused_runtime_rows':[[27,1]],
        'whole_tape_endpoints_checked':True,'primary_registers_vary_without_source_invariant_filter':True,
        'gap_values':[64,81,98],'nonempty_spare_lengths':[1,2,3,4,5],
        'seconds':time.monotonic()-began,
        'scope':'Finite fresh fixtures only; not a substitute for unbounded symbolic replay.',
        'row_counts':[[q,b,n]for(q,b),n in sorted(used.items())]}
    (a.candidate/'literal-regression.json').write_text(json.dumps(out,indent=2)+'\n')
    with gzip.GzipFile(filename=str(a.candidate/'literal-regression-cases.json.gz'),mode='wb',mtime=0)as f:
        f.write((json.dumps(records,indent=2)+'\n').encode('ascii'))
    print(json.dumps({k:v for k,v in out.items()if k!='row_counts'},indent=2),flush=True)

if __name__=='__main__':main()
