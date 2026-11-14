#!/usr/bin/env python3
"""Rebuild and symbolically verify the stride-two, H/X-swapped 195-state machine.

Usage: python3 verify_even195_hx.py PRIMARY_CONSTRUCTION_DIR --out OUTPUT_DIR
The primary construction directory supplies the unmodified PA194 compiler,
symbolic runtime, references, native table and source grammar. Retain its
licenses. This checks physical/source artifacts, not the logical calibration
or a proof-assistant kernel theorem. Python 3.10+, standard library, no -O.
"""
from pathlib import Path
import argparse, hashlib, json, sys


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('primary',type=Path)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    if not __debug__:raise SystemExit('Run without -O.')
    sys.path.insert(0,str(args.primary))
    import compiler as c
    primary=(args.primary/'tables/pa194.native.tm').read_bytes()
    assert hashlib.sha256(primary).hexdigest()=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
    rows={}
    for line in primary.decode().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
    old=dict(rows)
    assert 3000 not in {q for q,b in rows}
    rows[110,1]=(1,True,3000)
    rows[3000,0]=(0,True,14)
    rows[3000,1]=(1,True,8)
    assert rows[21,1]==(0,True,60) and rows[45,1]==(0,True,55)
    rows[21,1]=(0,True,55)
    rows[45,1]=(0,True,60)
    physical=[6,2,0,4,3,8,7,5,1]
    c.PHYSICAL[:]=physical
    nodes=c.raw_nodes()
    assert nodes['node27']==('node25','node26')
    nodes['node27']=('node25',(('leaf','inc',0),'node26'))
    c.raw_nodes=lambda:nodes
    sites,instructions,contracts=c.source(c.read_grammar(args.primary/'source/pa194.grammar.json'))
    validation=c.validate(rows,contracts)
    assert validation['ok'] and len(contracts)==4781 and len(sites)==3674,validation
    assert all(rows[q,b]==old[q,b] for q in c.BOXSTATES for b in (0,1))
    controls={q for q,b in rows}
    assert len(controls)==195 and len(rows)==390
    assert {t for _,_,t in rows.values()}-controls=={254}
    labels=[74];index={74:0}
    for q in labels:
        for bit in (0,1):
            n=rows[q,bit][2]
            if n!=254 and n not in index:index[n]=len(labels);labels.append(n)
    assert len(labels)==195
    dense={(index[q],b):(w,d,195 if n==254 else index[n])for(q,b),(w,d,n)in rows.items()}
    def text(table):return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'for(q,b),(w,d,n)in sorted(table.items()))
    native_text,dense_text=text(rows),text(dense)
    # Complete finite-support equality with the observed canonical source frame.
    sh=-2;pc=40;values=[0,1,0,0,0,0,4,0,0]+[1]*29
    expected={sh-1,sh+48}
    expected.update(sh+j for j,b in enumerate(sites[pc][0])if b)
    pos=sh+49
    for v in values:
        pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
    q,h,ones=74,0,set()
    for step in range(1,44095):
        w,d,q=rows[q,int(h in ones)]
        (ones.add if w else ones.discard)(h);h+=1 if d else -1
        assert q!=254
    assert(q,h,ones)==(84,sh,expected)
    logical=[values[physical[r]] for r in range(9)]
    assert logical==[4,0,0,0,0,0,0,0,1]
    seed=dict(steps=44094,native_state=q,head=h,source_pc=pc,gap=0,
              physical_registers=values,logical_registers=logical,
              one_cells=sorted(ones),complete_tape_equality=True)
    # The explicit finite source bridge ends at a fresh candidate boundary.
    reg=list(logical);ip=pc;trace=[]
    while not(ip==25 and reg==[4,0,0,0,0,0,0,0,0]):
        assert len(trace)<100
        code=instructions[ip];trace.append(dict(pc=ip,registers=list(reg),instruction=code))
        if code[0]=='inc':_,r,ip=code;reg[r]+=1
        elif code[0]=='dec':
            _,r,z,p=code
            if reg[r]:reg[r]-=1;ip=p
            else:ip=z
        elif code[0]=='jump':ip=code[1]
        else:raise AssertionError('Unexpected source halt in finite bridge')
    assert len(trace)==48
    trace.append(dict(pc=ip,registers=reg))
    receipt=dict(working_states=195,transitions=390,graph_reachable_working_states=195,
                 native_start=74,native_halt=254,dense_start=0,dense_halt=195,
                 source_sites=len(sites),symbolic_contracts=validation,
                 logical_to_physical=physical,arithmetic_box_rows_unchanged=True,
                 startup=seed,source_bridge_steps=48,clean_candidate=4,
                 sha256=dict(native=hashlib.sha256(native_text.encode()).hexdigest(),dense=hashlib.sha256(dense_text.encode()).hexdigest()),
                 kernel_checked=False,
                 scope='Physical/source certificate; the stride-two enumeration completeness and inherited logical PA calibration are separate mathematical arguments.')
    args.out.mkdir(parents=True,exist_ok=True)
    for name,data in [('even195HX.native.tm',native_text),('even195HX.tm',dense_text),('even195HX.labels.json',json.dumps(labels+[254])+'\n'),('verification.json',json.dumps(receipt,indent=2)+'\n'),('seed_bridge.json',json.dumps(trace,indent=2)+'\n'),('source.sites.json',json.dumps([[''.join(map(str,p)),op,r]for p,op,r in sites])+'\n'),('source.instructions.json',json.dumps(instructions)+'\n')]:
        (args.out/name).write_text(data)
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
