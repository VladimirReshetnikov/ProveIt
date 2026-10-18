"""Standalone literal checks supporting the ordinary branch-borrowing proof.

The proof is in borrow242_proof.md. This checker validates its finite table
hypotheses and its two symbolic whole-tape blocks. The optional blank check is
finite evidence only and is not the premise of the halting-equivalence proof.
"""
import argparse,hashlib,json,pathlib

OLD_SHA='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
NEW_SHA='6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0'

def parse(raw):
    rows={};start=None
    for line in raw.decode().splitlines():
        if not line:continue
        if line.startswith('#! start '):
            assert start is None;start=int(line.split()[-1]);continue
        if line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        assert b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in rows
        rows[q,b]=(w,1 if d=='R' else -1,t)
    states={q for q,b in rows}
    assert set(rows)=={(q,b) for q in states for b in (0,1)}
    assert {t for w,d,t in rows.values()}-states=={254}
    assert start==95
    return rows

def symbolic_run(rows,steps,neighbor):
    # Unknown exterior cells have distinct symbolic values. No executed read
    # is allowed to depend on any of them. Writes alter only this finite map.
    tape={0:0,1:neighbor};head=0;q=11;trace=[]
    for tick in range(steps):
        b=tape.get(head,('exterior',head))
        assert b in (0,1),(q,head,b)
        w,d,t=rows[q,b];tape[head]=w;head+=d;q=t
        trace.append([q,head,dict(tape)])
    return q,head,tape,trace

def concrete_run(rows,steps):
    ones=set();q=95;head=0;delays=0
    for tick in range(steps):
        assert q!=254,('unexpected halt',tick)
        b=int(head in ones)
        if q==11 and b==0 and head+1 not in ones:delays+=1
        w,d,q=rows[q,b]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    return q,head,ones,delays

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--baseline',type=pathlib.Path,required=True)
    ap.add_argument('--candidate',type=pathlib.Path,default=pathlib.Path(__file__).with_name('zfc_borrow242_old.tm'))
    ap.add_argument('--output',type=pathlib.Path,default=pathlib.Path(__file__).with_name('borrow242_verification.json'))
    ap.add_argument('--blank-prefix',action='store_true');args=ap.parse_args()
    oldraw=args.baseline.read_bytes();newraw=args.candidate.read_bytes()
    assert hashlib.sha256(oldraw).hexdigest()==OLD_SHA
    assert hashlib.sha256(newraw).hexdigest()==NEW_SHA
    old=parse(oldraw);new=parse(newraw)
    assert len(old)==486 and len(new)==484
    expected={k:v for k,v in old.items() if k[0]!=15}
    expected[11,0]=(0,1,27);expected[27,1]=(1,1,22)
    assert new==expected
    assert all(t!=15 for w,d,t in new.values())
    incoming={q:sorted([s,b,w,d] for (s,b),(w,d,t) in old.items() if t==q) for q in [15,18,27,47,65]}
    assert incoming[15]==[[11,0,0,1]]
    for q in [18,47,65]:
        assert all((w,d)==(0,1) for s,b,w,d in incoming[q])
    assert incoming[27]==[[18,0,0,-1],[47,0,0,-1],[65,0,0,-1]]
    ordinary=0
    for (q,b),e in new.items():
        if (q,b) in [(11,0),(27,1)]:continue
        assert e==old[q,b] and e[2]!=15
        ordinary+=1
    blocks=[]
    for bit,oldclock,newclock,target in [(0,2,4,21),(1,2,2,22)]:
        a=symbolic_run(old,oldclock,bit);b=symbolic_run(new,newclock,bit)
        assert a[:3]==b[:3]==(target,2,{0:0,1:bit})
        blocks.append({'neighbor':bit,'old_clock':oldclock,'new_clock':newclock,
                       'target':target,'head':2,'old_trace':a[3],'new_trace':b[3]})
    report={'status':'PASS','source_commit':'e58338db7545909907e07a7603e8eb88625c527a',
            'old_sha256':OLD_SHA,'new_sha256':NEW_SHA,'working_states':242,
            'rows':484,'start':95,'halt':254,'ordinary_rows':ordinary,
            'invariant_incoming_rows':incoming,'symbolic_blocks':blocks,
            'scope':'Finite literal hypotheses and symbolic blocks for ordinary proof; not a proof-assistant theorem.'}
    if args.blank_prefix:
        a=concrete_run(old,407967);n=407967+2*a[3]
        b=concrete_run(new,n);assert a[:3]==b[:3]
        report['blank_prefix']={'old_steps':407967,'new_steps':n,'delay_blocks':a[3],
            'state':b[0],'head':b[1],'one_count':len(b[2]),
            'one_positions_sha256':hashlib.sha256(json.dumps(sorted(b[2]),separators=(',',':')).encode()).hexdigest(),
            'complete_frame_equal':True}
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['symbolic_blocks','invariant_incoming_rows']}))

if __name__=='__main__':main()
