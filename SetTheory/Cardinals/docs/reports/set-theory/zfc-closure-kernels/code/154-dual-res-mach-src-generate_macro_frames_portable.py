#!/usr/bin/env python3
"""Generate independently checked finite K219 macro fixtures.

Requires only Python's standard library and the inherited independent runtime
module from the extracted K221 package. Run generate_frames_portable.py first.
Every reference output is checked against a separate register-level contract.
The fixtures are finite search observations, never an unbounded mutant proof.
"""
from pathlib import Path
import argparse,hashlib,itertools,json,struct,sys,time
from verify_runtime_portable import read_table,validate_sites

E_PREFIXES=['111010010011101111000','11101001001110111110',
            '1110100101100','111110']

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True,help='Extracted K221 package')
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--ordinary',type=Path,required=True,help='Checked ordinary fixture directory')
    ap.add_argument('--mode',choices=['equality','refill','gate','combined'],required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required.')
    sys.path.insert(0,str(args.baseline.resolve()/'portable/runtime/vendor'))
    import independent_runtime as r
    table=read_table(args.table);sites=json.loads(args.sites.read_text());validate_sites(sites)
    assert len(sites)==4744,'This generator describes the supplied K219 source.'
    assert [next(i for i,x in enumerate(sites)if x[0].startswith(p))for p in E_PREFIXES]==[4567,4585,4599,4708]
    out=args.output;out.mkdir(parents=True,exist_ok=True)
    ordinary=json.loads((args.ordinary/'frame_metadata.json').read_text())
    raw=(args.ordinary/'frames.bin').read_bytes()
    nf,size,offset=struct.unpack_from('<3i',raw);assert nf==len(ordinary)and(size,offset)==(512,128)
    stride=20+2*size;frames=[];metadata=[];witnesses={row:[]for row in table}
    low,high=sites[4563][0],sites[4597][0];begin=time.monotonic()
    mode=args.mode
    do_gate=mode in('gate','combined');do_refill=mode in('refill','combined')
    e_indices=range(4)if mode=='equality'else([2,3]if mode=='combined'else[])
    inside=set(range(4563,4597))if do_gate else set()
    if do_refill:inside.update(range(2,9))
    for i,row in enumerate(sites):
        if any(row[0].startswith(E_PREFIXES[j])for j in e_indices):inside.add(i)
    opens={};intervals={}

    def tape_bytes(ones):
        a=bytearray(size)
        for x in ones:assert 0<=x+offset<size;a[x+offset]=1
        return a

    def add(data,m):
        k=len(frames);frames.append(data);metadata.append(m)
        for row in map(tuple,m['used_rows']):
            if len(witnesses[row])<2:witnesses[row].append(k)

    for k,m in enumerate(ordinary):
        if m['ordinal']not in inside:add(raw[12+k*stride:12+(k+1)*stride],m)
    ordinary_count=len(frames)

    def run_macro(ordinal,ident,pc,regs,output_pc,output_regs,spares,gap,extra,interval=None):
        initial=r.frame(pc,regs,[1]);ones=initial.copy();q,h=84,0;used=set()
        for tick in range(500000):
            if tick and q==254:raise AssertionError(('macro halted',ordinal,regs))
            if tick and r.clean_dispatch(96 if q==84 else q,h,ones):
                code=''.join(str(int(h+j in ones))for j in range(52))
                internal=(interval[0].ljust(52,'0')<=code<interval[1].ljust(52,'0'))if interval else code.startswith(pc)
                if not internal:break
            bit=int(h in ones);used.add((q,bit));w,d,q=table[q,bit]
            if w:ones.add(h)
            else:ones.discard(h)
            h+=d
        else:raise AssertionError(('macro timeout',ordinal,regs))
        shift=extra.pop('_shift',0)
        expected={p-shift for p in r.frame(output_pc,output_regs,spares,gap)}
        assert(q,h,ones)==(84,-shift,expected),(ordinal,regs,q,h,shift)
        flags=4|(ident<<3)
        info=dict(ordinal=ordinal,positive=False,registers=regs,spares=[1],steps=tick,
                  used_rows=sorted(used),macro=ident,**extra)
        add(struct.pack('<5i',ordinal,flags,q,h+offset,tick)+tape_bytes(initial)+tape_bytes(ones),info)
        if interval:intervals[ident]=interval
        else:opens[ident]=pc

    if do_gate:
        for a,b,c in itertools.product(range(5),repeat=3):
            for context in range(3):
                regs=[3,0,0,c,b,a,0,0,0]
                if context==1:regs[1]=3;regs[2]=3;regs[8]=1
                if context==2:regs[0]=4;regs[1]=1;regs[2]=1;regs[8]=3
                rejected=a==c or b==c;result=regs.copy();result[3:8]=[0]*5
                if rejected:result[1]=0
                gap=a+2*b+4*c+(regs[1]if rejected else 0)
                run_macro(4563,0,low,regs,high,result,[1]*(1+3*c+b),gap,
                          dict(interval=[low,high],a=a,b=b,c=c,context=context,capture_rejected=rejected),[low,high])

    for j in e_indices:
        prefix=E_PREFIXES[j];ident=j if mode=='equality'else j-1
        ordinal=next(i for i,row in enumerate(sites)if row[0].startswith(prefix))
        prototype=next(m['registers']for m in ordinary if m['ordinal']==ordinal)
        for other in(prototype,[1]*9):
            for x in range(9):
                for y in([1]if mode=='combined'and j==2 else range(9)):
                    regs=other.copy();regs[5]=x;regs[6]=y
                    nxt,overflow=r.inc(prefix if x==y else r.strip(prefix,'0',1))
                    result=regs.copy();result[5]=result[6]=0
                    run_macro(ordinal,ident,prefix,regs,nxt,result,[1],x+y+overflow,
                              dict(prefix=prefix,equal=x==y,_shift=overflow))

    if do_refill:
        ident=3 if mode=='combined'else 0
        for n in(3,4,5,8,13):
            for other in range(3):
                regs=[0]*9;regs[0]=n
                if other==1:regs[1]=regs[2]=regs[5]=3;regs[4]=1
                if other==2:regs[4]=3
                result=regs.copy();result[0]=n+1;result[8]=n
                run_macro(2,ident,'01',regs,'10',result,[1]*(3*n+2),2*n,
                          dict(prefix='01',np=n,other_mode=other))

    with(out/'frames.bin').open('wb')as f:
        f.write(struct.pack('<3i',len(frames),size,offset))
        for frame in frames:f.write(frame)
    (out/'frame_metadata.json').write_text(json.dumps(metadata,separators=(',',':'))+'\n')
    (out/'witnesses.txt').write_text(''.join(' '.join(map(str,[q,b]+(xs+[-1,-1])[:2]))+'\n'for(q,b),xs in sorted(witnesses.items())))
    (out/'macros.txt').write_text(''.join(f'{i} {p}\n'for i,p in sorted(opens.items())))
    (out/'intervals.txt').write_text(''.join(f'{i} {a} {b}\n'for i,(a,b)in sorted(intervals.items())))
    report=dict(scope='Independently checked finite macro observations; no unbounded mutant proof.',
                mode=mode,total_frames=len(frames),ordinary_frames=ordinary_count,
                macro_frames={i:sum(m.get('macro')==i for m in metadata)for i in set(opens)|set(intervals)},
                maximum_reference_steps=max(m['steps']for m in metadata),
                uncovered_rows=[list(row)for row,xs in sorted(witnesses.items())if not xs],
                inputs_sha256={name:hashlib.sha256(getattr(args,name).read_bytes()).hexdigest()for name in('table','sites')},
                frames_sha256=hashlib.sha256((out/'frames.bin').read_bytes()).hexdigest(),seconds=time.monotonic()-begin)
    (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
