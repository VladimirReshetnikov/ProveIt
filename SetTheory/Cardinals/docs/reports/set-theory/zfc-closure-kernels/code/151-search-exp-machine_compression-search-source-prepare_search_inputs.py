#!/usr/bin/env python3
"""Portable input preparation and full collected-window checking.
Python3 standard library only. These checks concern finite representative
windows, not arbitrary natural register valuations or an equiconsistency proof.
"""
import argparse
import json
from pathlib import Path

RADIUS=7
FUEL=97

def native(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert d in ('L','R') and (q,b)not in table
        table[q,b]=(w,1 if d=='R' else -1,z)
    states=sorted({q for q,b in table})
    assert len(states)==218 and max(states)<303
    return table,states

def read_contexts(path):
    lines=path.read_text().splitlines();n=int(lines[0]);table={};states=[]
    for line in lines[1:n+1]:
        q,w0,d0,z0,w1,d1,z1=map(int,line.split());states.append(q)
        table[q,0]=(w0,d0,z0);table[q,1]=(w1,d1,z1)
    count=int(lines[n+1]);patterns={q:[]for q in states}
    for line in lines[n+2:]:
        q,m=map(int,line.split());patterns[q].append(m)
    assert sum(map(len,patterns.values()))==count
    return table,states,patterns,lines[:n+1]

def frames(args):
    table,states=native(args.table);sites=json.loads(args.sites.read_text())
    assert len(sites)==4744
    masks=json.loads(args.binary_invariant.read_text())if args.binary_invariant else [[]for _ in sites]
    assert len(masks)==len(sites)
    lines=[str(len(states))]+[' '.join(map(str,[q,*table[q,0],*table[q,1]]))for q in states]
    lines.append(str(len(sites)))
    for (pc,op,arg),allowed in zip(sites,masks):
        arg=-1 if arg is None else arg
        lines.append(' '.join(map(str,[pc,arg,len(allowed),*allowed])))
    args.output.write_text('\n'.join(lines)+'\n')
    print('Wrote',args.output,'with',len(sites),'source sites.')

def sample(args):
    table,states,patterns,header=read_contexts(args.contexts);out=[]
    for q in states:
        for bit in (0,1):
            a=sorted(m for m in patterns[q]if(m>>RADIUS)&1==bit)
            if a:
                out.extend((q,m)for m in sorted({a[round(i*(len(a)-1)/15)]for i in range(16)}))
    args.output.write_text('\n'.join(header+[str(len(out))]+[f'{q} {m}'for q,m in out])+'\n')
    print('Wrote',len(out),'sample contexts to',args.output)

def verify(args):
    old,states,patterns,header=read_contexts(args.contexts);path_cache={}
    def old_path(q,m):
        key=q,m
        if key not in path_cache:
            result=[];h=0
            for _ in range(FUEL):
                if q==254 or not -RADIUS<=h<=RADIUS:break
                bit=(m>>(h+RADIUS))&1;w,d,q=old[q,bit]
                m=(m&~(1<<(h+RADIUS)))|(w<<(h+RADIUS));h+=d
                result.append((q,h,m))
            path_cache[key]=result
        return path_cache[key]
    def check(new,kp,dr,shift):
        for oq in (dr,kp):
            for bit in (0,1):
                ms=sorted(m for m in patterns[oq]if(m>>RADIUS)&1==bit)
                if len(ms)>2:ms=[ms[0],ms[-1],*ms[1:-1]]
                for original_m in ms:
                    goals={(kp if q==dr else q,h+(shift if q==dr else 0),m)for q,h,m in old_path(oq,original_m)}
                    q=kp;h=shift if oq==dr else 0;m=original_m;seen=set()
                    for _ in range(FUEL):
                        if q==254 or not -RADIUS<=h<=RADIUS:return [oq,bit,original_m,'exit']
                        key=q,h,m
                        if key in seen:return [oq,bit,original_m,'cycle']
                        seen.add(key);b=(m>>(h+RADIUS))&1;w,d,q=new[q,b]
                        m=(m&~(1<<(h+RADIUS)))|(w<<(h+RADIUS));h+=d
                        if (q,h,m)in goals:break
                    else:return [oq,bit,original_m,'fuel']
        return None
    records=[]
    for index,line in enumerate(args.specs.read_text().splitlines()):
        if not line:continue
        tag,*fields=line.split();assert tag=='HIT'
        kp,dr,shift,w0,d0,z0,w1,d1,z1=map(int,fields)
        new={(q,b):(w,d+(shift if z==dr else 0),kp if z==dr else z)for(q,b),(w,d,z)in old.items()if q!=dr}
        new[kp,0]=(w0,d0,z0);new[kp,1]=(w1,d1,z1)
        witness=check(new,kp,dr,shift)
        records.append(dict(index=index,keeper=kp,drop=dr,shift=shift,passed=witness is None,first_failed_window=witness))
    result=dict(scope='Full check of this finite collected-window dataset only',radius=RADIUS,fuel=FUEL,specifications=len(records),survivors=sum(r['passed']for r in records),records=records)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('Checked',len(records),'preliminary folds; survivors',result['survivors'])

if __name__=='__main__':
    parser=argparse.ArgumentParser();sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('frames');p.add_argument('--table',type=Path,required=True);p.add_argument('--sites',type=Path,required=True);p.add_argument('--binary-invariant',type=Path);p.add_argument('--output',type=Path,required=True);p.set_defaults(func=frames)
    p=sub.add_parser('sample');p.add_argument('--contexts',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.set_defaults(func=sample)
    p=sub.add_parser('verify');p.add_argument('--contexts',type=Path,required=True);p.add_argument('--specs',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.set_defaults(func=verify)
    args=parser.parse_args();args.func(args)
