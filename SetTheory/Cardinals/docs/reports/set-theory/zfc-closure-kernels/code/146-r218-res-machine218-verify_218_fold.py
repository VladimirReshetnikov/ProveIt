#!/usr/bin/env python3
"""Independent finite complete-tape replay of the88/301/51 quotient witness.

This verifier does not invoke any search code.  The source-certified window
cover and its proof obligations remain explicit inputs.  Every witness has
strictly positive old and new duration and reads only supplied cells.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm'


def read(path):
    table={}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,z=line.split()
            table[int(q),int(b)]=int(w),1 if d=='R'else-1,int(z)
    return table


def main():
    T=read(BASE)
    quotient=lambda q:88 if q==301 else q
    U={(q,b):(w,d,quotient(z))for(q,b),(w,d,z)in T.items()if q!=301}
    U[88,0]=(0,-1,51)
    U[88,1]=(1,1,103)
    U[51,0]=(0,1,122)
    U[51,1]=(1,1,51)
    states={q for q,b in U}
    assert len(states)==218 and len(U)==436
    assert set(U)=={(q,b)for q in states for b in(0,1)}
    assert {z for w,d,z in U.values()}-states=={254}
    out=ROOT/'machine218/candidate218';out.mkdir(exist_ok=True)
    path=out/'candidate.tm'
    path.write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(U.items())))
    reports={}
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    for label,name in [('postinit','windows_postinit_r7.txt'),('full','windows_r7.txt')]:
        wp=ROOT/'machine218/windows219'/name
        cases=[]
        for line in wp.read_text().splitlines():
            q,x=map(int,line.split())
            if q in(88,301,51):cases.append((q,x))
        histogram=Counter();failures=[];witnesses=[]
        for q0,x in cases:
            initial={i-7 for i in range(15)if x&(1<<i)}
            goals={};oldq,oldh,oldones=q0,0,set(initial)
            for n in range(1,26):
                if not-7<=oldh<=7 or(oldq,0)not in T:break
                w,d,oldq=T[oldq,int(oldh in oldones)]
                if w:oldones.add(oldh)
                else:oldones.discard(oldh)
                oldh+=d
                goals.setdefault((quotient(oldq),oldh,frozenset(oldones)),n)
            newq,newh,newones=quotient(q0),0,set(initial);visited=[]
            for n in range(1,65):
                if not-7<=newh<=7 or(newq,0)not in U:break
                visited.append((newq,int(newh in newones)))
                w,d,newq=U[newq,int(newh in newones)]
                if w:newones.add(newh)
                else:newones.discard(newh)
                newh+=d
                key=(newq,newh,frozenset(newones))
                if key in goals:
                    oldn=goals[key]
                    histogram[f'{q0}/{(x>>7)&1}:{oldn},{n}']+=1
                    witnesses.append(dict(old_state=q0,window=x,old_steps=oldn,new_steps=n,
                                          endpoint=[newq,newh,sorted(newones)],new_rows=visited))
                    break
            else:n=64
            if (newq,newh,frozenset(newones))not in goals:
                failures.append(dict(old_state=q0,window=x,new_state=newq,new_head=newh,steps=n))
        (out/f'{label}_witnesses.json').write_text(json.dumps(witnesses,indent=2)+'\n')
        report=dict(status='POSITIVE_WHOLE_WINDOW_DIAMONDS_PASS'if not failures else'FAILED',
                    cases=len(cases),histogram=dict(histogram),failures=failures,
                    windows_sha256=sha(wp),witnesses_sha256=sha(out/f'{label}_witnesses.json'),
                    scope='Exact finite verification over supplied original-machine window cover. Every witness reads only known cells and preserves the complete tape outside them. Coverage requires the separate source invariant and symbolic projection proof.')
        reports[label]=report
        print(label,json.dumps({k:v for k,v in report.items()if k!='failures'}),flush=True)
    receipt=dict(status='CANDIDATE_FINITE_LOCAL_PROOF',working_states=218,rows=436,
                 old_table_sha256=sha(BASE),table_sha256=sha(path),verifier_sha256=sha(Path(__file__)),
                 quotient={'301':88},changed_rows={f'{q}/{b}':list(row)for(q,b),row in U.items()if T.get((q,b))!=row},
                 domains=reports,remaining_obligations='Fresh complete symbolic primitive interfaces, source decoder binding, and exact blank startup are independent obligations. No theorem of equivalence is asserted by this receipt alone.')
    (out/'local_proof.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('TABLE_SHA256',sha(path),flush=True)


if __name__=='__main__':main()
