#!/usr/bin/env python3
"""27-state comparison variant requiring a counter gap of at least THREE."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import compare_biased_counter as C
import json,hashlib,itertools,random
OUT=Path(__file__).resolve().parent

def compile_compare():
    T,start,ports,ids,aliases,guards=C.compile_compare()
    inv={i:q for q,i in ids.items()}|{i:q for q,i in ports.items()}
    drop={'failed_ones','failed_zero','failed_gap'}
    rows={(inv[q],b):(w,d,inv[t])for(q,b),(w,d,t)in T.items()if inv[q]not in drop}
    rows['restore_exhausted',0]=(1,'R','dummy_counter_one')
    rows['dummy_counter_one',0]=(1,'R','failed_gap_right')
    rows['dummy_counter_one',1]=(1,'R','reject')
    rows['failed_restore_left',0]=(1,'L','done_ones')
    names=[q for q in ids if q not in drop]+['dummy_counter_one'];names.remove('reject');names.append('reject')
    ni={q:i for i,q in enumerate(names)};P={'EQ':len(ni),'NEQ':len(ni)+1}
    result={(ni[q],b):(w,d,P[t]if t in P else ni[t])for(q,b),(w,d,t)in rows.items()}
    return result,ni['init'],P,ni

def main():
    T,s,P,ids=compile_compare();count=0;maxsteps=0;used=set()
    for a,b,i,gap,k in itertools.product(range(8),range(8),range(4),(3,4,8),range(1,5)):
        n,r=C.check(T,s,P,a,b,[1,2,5],i,gap,k=k);count+=1;maxsteps=max(maxsteps,n);used|=r
    rng=random.Random(202610180342)

    for trial in range(2000):
        a=rng.randrange(100);b=rng.randrange(100);other=[rng.randrange(1,30)for _ in range(rng.randrange(20))];i=rng.randrange(len(other)+1)
        gap=rng.randrange(3,30);c=rng.randrange(-50,51);k=rng.randrange(1,5)
        _,ss,end,hh=C.frame(a,b,other,i,gap,c,k)
        ext=[c-j for j in range(2,20)if rng.randrange(2)]+[end+j for j in range(20)if rng.randrange(2)]
        n,r=C.check(T,s,P,a,b,other,i,gap,c,k,ext);count+=1;maxsteps=max(maxsteps,n);used|=r
    text='# Gap at least THREE required; ports '+json.dumps(P)+'\n#! start '+str(s)+'\n'+''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(T.items()))
    (OUT/'compare_biased_counter_27.tm').write_text(text)
    base=json.loads((OUT/'compare_biased_counter_guards.json').read_text())['valid_reads_by_name'];guards={name:base.get(name,[0])for name in ids}
    result=dict(status='PASS',scope='Prepared-frame comparator with gap>=3; NOT valid on all gap2 inputs',states=len(ids),operational_states=len(ids)-1,ports=P,start=s,names=ids,tests=count,maximum_steps=maxsteps,table_sha256=hashlib.sha256(text.encode()).hexdigest(),valid_reads_by_name=guards,valid_reads_by_state={str(ids[q]):bs for q,bs in guards.items()})
    (OUT/'compare_biased_counter27_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
