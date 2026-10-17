#!/usr/bin/env python3
"""Measure GEN binders extracted from the current theorem's Cantor pair.

The first projection is surjective on theorem codes because Imp(i,0)=P(i,i).
The sum projection reaches every even binder. Logical calibration belongs to
the accompanying logical audit; the counts here charge actual emitted tables.
"""
import hashlib,json,time
import native_protocol_variants as v

def seq(a,b):return ('T',a,b)

def main():
    begun=time.monotonic();base,_=v.runtime.generate()
    unpair=seq(('D',1),('N',14))
    clearY=seq(('D',7),('C',1))
    first=seq(unpair,seq(clearY,('N',30)))
    summ=seq(unpair,seq(('N',11),('N',30)))
    records=[]
    for tag,binder in [('first',first),('sum',summ)]:
        gen=seq(binder,seq(('N',48),('N',58)))
        checks=[]
        for x in range(4):
            for y in range(4):
                value=(x+y)*(x+y+1)//2+y
                regs=[7,value,11,13,17,19,0,0,23]
                status,out,steps=v.closed_run(binder,regs)
                wanted=regs[:];wanted[1]=x if tag=='first' else x+y
                assert status=='normal' and out==wanted,(tag,x,y,status,out,wanted)
                checks.append([x,y,steps])
        edits={'1110100100100':gen,'111111':('N',42)}
        nodes,root=v.patch_path(edits)
        table,entry=v.emit(nodes,root,base)
        v.a.sites=v.native_sites(nodes,root);guards=v.runtime.guards();tracked=v.Tracking(table)
        check=v.runtime.certify(tracked,guards)
        result=dict(variant=tag,decoder_nodes=len(nodes),guards=len(guards),affine=check,
                    exact_integer_binder_checks=len(checks))
        if check['passed']:
            used=tracked.used|{(str(q),b) for q,b in v.audit.BOX_PAIRS}
            states={q for q,b in used}|{'64','96'}
            pruned={}
            for (q,b),(w,d,t) in table.items():
                if q not in states:continue
                if t not in states|{'254'}:
                    assert (q,b) not in used;t='64'
                pruned[q,b]=w,d,t
            result['working_states']=len(states)
            output=v.HERE/f'projected_gen_{tag}.tm';output.write_bytes(v.a.encoded(pruned))
            result['table_sha256']=hashlib.sha256(output.read_bytes()).hexdigest()
        records.append(result)
        print(json.dumps(result),flush=True)
    (v.HERE/'projected_gen_results.json').write_text(json.dumps(dict(scope=__doc__,records=records,seconds=time.monotonic()-begun),indent=2)+'\n')

if __name__=='__main__':main()
