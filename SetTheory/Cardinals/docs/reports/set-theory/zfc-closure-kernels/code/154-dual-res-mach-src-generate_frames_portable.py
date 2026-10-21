#!/usr/bin/env python3
"""Generate checked finite primitive fixtures for whole_primitive_folds.c.

Independent masks in --facts are an abstract overapproximation, not a claim
that each selected Cartesian minimum occurs on the actual blank-tape run.
"""
from pathlib import Path
import argparse, hashlib, json, struct, sys, time
from verify_runtime_portable import read_table, validate_sites


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--facts',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required.')
    sys.path.insert(0,str(args.baseline.resolve()/'portable/runtime/vendor'))
    import independent_runtime as r
    table=read_table(args.table);sites=json.loads(args.sites.read_text())
    validate_sites(sites);facts=json.loads(args.facts.read_text())
    out=args.output;out.mkdir(parents=True,exist_ok=True)
    size,offset=512,128;witnesses={row:[] for row in table}
    frames=[];metadata=[];begin=time.monotonic()

    def low(mask):
        assert type(mask) is int and mask>0
        return (mask&-mask).bit_length()-1

    def tape_bytes(ones):
        tape=bytearray(size)
        for x in ones:
            assert 0<=x+offset<size
            tape[x+offset]=1
        return bytes(tape)

    for ordinal,positive in facts['admitted_cases']:
        site=sites[ordinal];pc,op,arg=site
        regs=[low(mask) for mask in facts['facts'][ordinal]]
        assert len(regs)==9
        if op=='CD':regs[arg]=low(facts['facts'][ordinal][arg]&(~1 if positive else 1))
        spares=[1];initial=r.frame(pc,regs,spares)
        ones=initial.copy();q,h=84,0;used=set()
        for tick in range(10000):
            if tick and(q==254 or r.clean_dispatch(96 if q==84 else q,h,ones)):break
            bit=int(h in ones);used.add((q,bit));w,d,q=table[q,bit]
            if w:ones.add(h)
            else:ones.discard(h)
            h+=d
        else:raise AssertionError(('baseline timeout',ordinal,positive))
        if op=='CH':assert q==254
        else:
            want,_=r.expected(site,regs,spares)
            assert(q,h,ones)==(84,want[1],want[2]),(ordinal,positive)
        k=len(frames)
        for row in used:
            if len(witnesses[row])<2:witnesses[row].append(k)
        flags=int(positive)|(2 if op=='CI' else 0)
        frames.append(struct.pack('<5i',ordinal,flags,q,h+offset,tick)+tape_bytes(initial)+tape_bytes(ones))
        metadata.append(dict(ordinal=ordinal,positive=positive,registers=regs,spares=spares,steps=tick,used_rows=sorted(used)))
    with (out/'frames.bin').open('wb') as f:
        f.write(struct.pack('<3i',len(frames),size,offset))
        for frame in frames:f.write(frame)
    with (out/'witnesses.txt').open('w') as f:
        for(q,b),xs in sorted(witnesses.items()):
            f.write(' '.join(map(str,[q,b]+(xs+[-1,-1])[:2]))+'\n')
    (out/'frame_metadata.json').write_text(json.dumps(metadata,separators=(',',':'))+'\n')
    report=dict(scope='Finite source-admissible minimum-register frames; no universal conclusion.',
                frames=len(frames),states=len(table)//2,frame_bytes=size,offset=offset,
                uncovered_rows=[list(row) for row,xs in sorted(witnesses.items()) if not xs],
                total_baseline_steps=sum(m['steps'] for m in metadata),
                max_steps=max(m['steps'] for m in metadata),seconds=time.monotonic()-begin,
                inputs_sha256={name:hashlib.sha256(getattr(args,name).read_bytes()).hexdigest()
                               for name in ('table','sites','facts')})
    (out/'frames_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
