"""Falsify the naive six-leaf NIP graft with a concrete legal CI8 frame.

This is an intentionally rejected table edit, never a candidate claim.
The inherited sparse runtime checks exact states, head locations and tape cells.
"""
from pathlib import Path
import argparse,json,hashlib
import finite_runtime as r
HERE=Path(__file__).resolve().parent
PATCH={(46,0):(0,1,62),(46,1):(1,1,78),(62,0):(0,1,53),
       (62,1):(1,1,77),(77,0):(0,1,103)}

def source_sites():
    j=json.loads((HERE/'nip_source.json').read_text());s=j['structures']
    def walk(n,p):
        x=s[n]
        if isinstance(x[0],str):return [[p,*x]]
        return walk(x[0],p+'0')+walk(x[1],p+'1')
    return walk(j['root'],'')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--all-cases',action='store_true');args=ap.parse_args()
    base=r.table(HERE/'base237_old.tm');altered=dict(base);altered.update(PATCH)
    assert len({q for q,b in base})==len({q for q,b in altered})==237
    site=['01010','CI',8];regs=[0]*9;spares=[0]
    expected,logical=r.expected(site,regs,spares)
    old,oldsteps,oldtrace=r.run(base,site[0],regs,spares,trace=True)
    new,steps,trace=r.run(altered,site[0],regs,spares,trace=True)
    assert old==expected and new!=expected
    out=dict(status='REJECTED_NAIVE_GRAFT',scope='Concrete valid runtime-frame failure, not a statement about the blank run',
        baseline_sha256=hashlib.sha256((HERE/'base237_old.tm').read_bytes()).hexdigest(),
        site=site,logical_registers=regs,spares=spares,start_state=96,start_head=0,
        initial_one_cells=sorted(r.frame(site[0],regs,spares)),
        baseline_steps=oldsteps,altered_steps=steps,expected=r.describe(expected),actual=r.describe(new),
        tape_xor=sorted(expected[2]^new[2]),expected_logical=logical,
        row_patch=[dict(state=q,read=b,write=w,direction='R'if d==1 else'L',target=t)
                   for(q,b),(w,d,t)in sorted(PATCH.items())],
        baseline_trace_prefix=oldtrace[:20],altered_trace_prefix=trace[:20])
    (HERE/'nip_counterexample.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k]for k in('status','site','baseline_steps','altered_steps','tape_xor')}))
    if args.all_cases:
        failures=[];checked=0
        for i,s in enumerate(source_sites()):
            for positive in ((False,True)if s[1]=='CD'else(False,)):
                vals=[0]*9
                if positive:vals[s[2]]=1
                want=r.expected(s,vals,[0]);actual,n,_=r.run(altered,s[0],vals)
                ok=actual[0]==254 if want is None else actual==want[0]
                if not ok:
                    failures.append(dict(index=i,site=s,positive=positive,steps=n,
                        state=actual[0],head=actual[1],
                        tape_xor=sorted(actual[2]^want[0][2])if want else None))
                checked+=1
        saved=json.loads((HERE/'receipts/nip_finite_failures.json').read_text())
        assert failures==saved
        print(json.dumps(dict(cases=checked,failures=len(failures),same_saved_receipt=True)))

if __name__=='__main__':main()
