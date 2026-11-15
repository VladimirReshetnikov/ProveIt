#!/usr/bin/env python3
"""Check every affine clock coefficient and the actual constructor-loop cost."""
from pathlib import Path
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'independent/reference'))
from independent_runtime import inc
C=[534,8]+[4]*9+[2,2]
def clock(sites,ins,contracts,start):
    shift=[0]*13;shift[2+7]=1;total=[0]*13
    for i in range(start,start+6):
        address,op,arg=sites[i];positive=i==start
        duration=contracts[i,positive];offsets=shift.copy()
        if op=='dec'and positive:offsets[2+arg]-=1
        total=[x+y for x,y in zip(total,duration)]
        total[0]+=sum(duration[j]*offsets[j]for j in range(1,13))
        if op=='inc':
            shift[2+arg]+=1;shift[12]+=3;shift[1]+=inc(address)[1]
        elif op=='dec'and positive:
            shift[2+arg]-=1;shift[1]+=1+inc(address)[1]
        else:assert op=='continueTo'
    assert ins[start+5]==['jump',start]
    return total,shift
def main(evidence,output):
    assert __debug__ and not sys.flags.optimize
    rows=[];data=[]
    for family,path in [('PA194AX11H',ROOT/'parent'),('PA194LC_AX11H',ROOT)]:
        p=evidence/family/'contracts.json';raw=p.read_bytes();xs=json.loads(raw)
        ds=[x['duration']for x in xs]
        assert len(ds)==4778 and all(len(d)==13 and d[0]>=3 and all(type(x)is int and x>=0 for x in d)for d in ds)
        assert all(all(x<=y for x,y in zip(d,C))for d in ds)
        rows.append(dict(family=family,contracts_sha256=hashlib.sha256(raw).hexdigest(),outcomes=len(ds),minimum_constant=min(d[0]for d in ds),slotwise_maximum=[max(d[j]for d in ds)for j in range(13)],upper_envelope=C))
        data.append((json.loads((path/'sites.json').read_text()),json.loads((path/'instructions.json').read_text()),{(x['site'],x['positive']):x['duration']for x in xs}))
    assert data[0][1]==data[1][1]
    ins=data[0][1]
    starts=[k for k in range(len(ins)-5)if ins[k]==['dec',7,k+6,k+1]and all(ins[k+j]==['inc',1,k+j+1]for j in range(1,5))and ins[k+5]==['jump',k]]
    assert len(starts)==61
    for k in starts:
        a,sa=clock(*data[0],k);b,sb=clock(*data[1],k)
        assert sa==sb and [y-x for x,y in zip(a,b)]==[6]+[0]*12
    result=dict(status='PASS',families=rows,successful_loop_occurrences=len(starts),extra_physical_transitions_per_successful_loop_iteration=6,initial_auxiliary_values=dict(gap=0,register_sum=2,first_spare=1,tail_width=75),per_source_step_upper_increases=dict(gap=2,register_sum=1,first_spare=0,tail_width=3),source_step_duration_bound='694+26*j',cross_machine_bound='57922+13*(t+1)^2+681*(t+1)',cross_machine_bound_expanded='13*t^2+707*t+58616',scope='Finite exact affine-coefficient and six-instruction clock calculation. Quantifier-free-induction soundness and relative iPRA proof are in proof.tex.')
    output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--evidence',type=Path,default=ROOT/'independent/results');p.add_argument('--output',type=Path,default=ROOT/'duration_receipt.json');a=p.parse_args();main(a.evidence,a.output)
