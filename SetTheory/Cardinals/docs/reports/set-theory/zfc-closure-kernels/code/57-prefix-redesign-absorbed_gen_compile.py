#!/usr/bin/env python3
"""Measure a GEN constructor that absorbs a Cantor projection into copyH.

unpair(T); copyHtail; Y->X; pair(X,T); times4; add2 computes
All(second(unpair(oldT)),oldH) while replacing H by oldH+first(unpair(oldT)).
The complete AX source soundness/completeness is a separate logical argument.
"""
from functools import lru_cache
import hashlib,json,time
import native_protocol_variants as v

def seq(a,b):return ('T',a,b)
@lru_cache(None)
def brackets(word):
    if len(word)==1:return (word[0],)
    return tuple(seq(a,b) for k in range(1,len(word)) for a in brackets(word[:k]) for b in brackets(word[k:]))

def pair(a,b):return (a+b)*(a+b+1)//2+b

def main():
    begun=time.monotonic();base,_=v.runtime.generate()
    unpair=seq(('D',1),('N',14))
    word=(unpair,('N',47),('N',11),('N',34),('N',55),('N',52))
    records=[];best=None
    for index,gen in enumerate(brackets(word)):
        for x,y,h in ((0,0,0),(0,1,2),(2,0,3),(2,3,1)):
            regs=[7,pair(x,y),11,13,17,h,0,0,23]
            status,out,steps=v.closed_run(gen,regs,fuel=100000)
            wanted=regs[:];wanted[1]=4*pair(y,h)+2;wanted[5]=h+x
            assert status=='normal' and out==wanted,(index,x,y,h,status,out,wanted)
        nodes,root=v.patch_path({'1110100100100':gen,'111111':('N',42)})
        table,entry=v.emit(nodes,root,base)
        v.a.sites=v.native_sites(nodes,root);guards=v.runtime.guards();tracked=v.Tracking(table)
        check=v.runtime.certify(tracked,guards)
        result=dict(index=index,decoder_nodes=len(nodes),guards=len(guards),affine=check)
        if check['passed']:
            used=tracked.used|{(str(q),b) for q,b in v.audit.BOX_PAIRS}
            states={q for q,b in used}|{'64','96'};pruned={}
            for (q,b),(w,d,t) in table.items():
                if q not in states:continue
                if t not in states|{'254'}:
                    assert (q,b) not in used;t='64'
                pruned[q,b]=w,d,t
            result['working_states']=len(states)
            if best is None or len(states)<best['working_states']:
                best=result.copy();best['expression']=gen
                output=v.HERE/'absorbed_gen_best.tm';output.write_bytes(v.a.encoded(pruned))
                best['table_sha256']=hashlib.sha256(output.read_bytes()).hexdigest()
                print('BEST',json.dumps(best),flush=True)
        records.append(result)
    (v.HERE/'absorbed_gen_results.json').write_text(json.dumps(dict(scope=__doc__,best=best,records=records,seconds=time.monotonic()-begun),indent=2)+'\n')
    print('DONE',len(records),'best',best['working_states'] if best else None,'seconds',time.monotonic()-begun,flush=True)

if __name__=='__main__':main()
