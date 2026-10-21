#!/usr/bin/env python3
"""Independent dense blank, literal delta, and inherited-fold review of K215.

Uses only Python's standard library. It does not replay the universal unary
runtime proof; that is a separate required receipt for these exact table bytes.
"""
import argparse,gzip,hashlib,json,sys
from pathlib import Path
from collections import Counter


def read(path, halt=254):
    t={};start=None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):start=int(line[9:]);continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        assert b in(0,1) and w in(0,1) and d in('L','R') and(q,b)not in t
        t[q,b]=w,1 if d=='R' else -1,z
    states={q for q,b in t}
    assert start in states and halt not in states
    assert set(t)=={(q,b)for q in states for b in(0,1)}
    assert {z for _,_,z in t.values()}-states=={halt}
    return t,start


def emit(t,start=0):
    return '#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))


def incoming(t,q):return [(x,b,w,d)for(x,b),(w,d,z)in sorted(t.items())if z==q]


def unfold(t,keep,drop,selector,zero_target,one_target):
    assert drop not in {q for q,b in t} and keep!=0
    assert t[keep,0]==(0,-1,selector)
    inc=incoming(t,keep);assert inc and {w for x,b,w,d in inc}=={0,1}
    assert all(d==1 for x,b,w,d in inc)
    p0,p1=t[selector,0],t[selector,1]
    assert p0[:2]==(0,1) and p1[:2]==(1,1)
    assert t[p0[2],0]==(0,1,zero_target) and t[p1[2],0]==(0,1,one_target)
    u=dict(t);u[keep,0]=(0,1,one_target);u[drop,0]=(0,1,zero_target);u[drop,1]=t[keep,1]
    for x,b,w,d in inc:
        if w==0:u[x,b]=w,d,drop
    phi=lambda q:keep if q==drop else q
    for(q,b),(w,d,z)in u.items():
        if (q,b)not in((keep,0),(drop,0)):
            assert t[phi(q),b]==(w,d,phi(z))
    assert all(w==1 and d==1 for x,b,w,d in incoming(u,keep))
    assert all(w==0 and d==1 for x,b,w,d in incoming(u,drop))
    return u,{'keep':keep,'drop':drop,'selector':selector,'before_working_states':len(u)//2,'after_working_states':len(t)//2,'incoming_one_origin':incoming(u,keep),'incoming_zero_origin':incoming(u,drop),'providers':[p0[2],p1[2]],'zero_origin_target':zero_target,'one_origin_target':one_target,'unchanged_rows_commute_with_state_map':True,'scope':'All initial binary tapes from state 0: one old step corresponds to one or three new steps, with identical whole tape and head at matched boundaries.'}


def fragment(t,b):
    tape={-1:b,0:0};q,h=81,0;trace=[]
    for _ in range(3):
        bit=tape.get(h,0);w,d,z=t[q,bit];trace.append([q,h,bit,w,d,z]);tape[h]=w;q=z;h+=d
    return (q,h,tuple(sorted(tape.items()))),trace


def dense(t,start,steps,expected_trace=None):
    offset=4096;a=bytearray(16384);q=start;h=0;used=set();minimum=maximum=0
    for tick in range(steps):
        ix=h+offset;assert0le(ix,len(a));b=a[ix];w,d,z=t[q,b]
        if expected_trace is not None:assert [q,h,b,w,d,z]==expected_trace[tick]
        used.add((q,b));a[ix]=w;q=z;h+=d;minimum=min(minimum,h);maximum=max(maximum,h)
    return {'state':q,'head':h,'one_cells':[i-offset for i,v in enumerate(a)if v],'visited_interval':[minimum,maximum],'used_rows':len(used),'dense_capacity':len(a),'offset':offset}


def assert0le(i,n):
    assert 0<=i<n


def decode(r):
    h=r['head'];o=set(r['one_cells']);assert min(o)==h-1
    header=min(x for x in o if x>h-1);assert header>=h+64
    assert not any(x in o for x in range(h,header))
    p=header+1;values=[]
    while p<=max(o):
        assert p not in o and p+1 in o;p+=1;start=p
        while p in o:p+=1
        values.append(p-start-1)
    assert p==max(o)+1 and len(values)>=10
    return {'gap':header-h-64,'registers':[values[i]for i in(6,2,0,4,3,7,8,5,1)],'spares':values[9:]}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in('table','partial','k217','startup','output','work'):ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--canonical',type=Path,help='Optional exact canonical table to compare and replay')
    args=ap.parse_args()
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
    n,start=read(args.table);p,ps=read(args.partial);old,os=read(args.k217)
    assert start==ps==os==0 and len(n)==430 and len(p)==432
    q={x for x,b in n};pq={x for x,b in p};assert pq-q=={185}and not q-pq
    reachable={0};todo=[0]
    while todo:
        x=todo.pop()
        for b in(0,1):
            z=n[x,b][2]
            if z!=254 and z not in reachable:reachable.add(z);todo.append(z)
    assert reachable==q
    delta=[{'state':x,'read':b,'old':list(p[x,b]),'new':list(n[x,b])if(x,b)in n else None}for x,b in sorted(p)if p[x,b]!=n.get((x,b))]
    u216,second=unfold(n,164,183,201,150,77)
    u217,first=unfold(u216,69,400,213,104,105)
    args.work.mkdir(parents=True,exist_ok=True)
    (args.work/'unfolded216.native.tm').write_text(emit(u216))
    (args.work/'unfolded217.native.tm').write_text(emit(u217))
    helper=[]
    for b in(0,1):
        want,ot=fragment(old,b);got,nt=fragment(n,b);assert got==want
        assert got[1]==1 and dict(got[2])=={-1:b,0:0}
        helper.append({'left_bit':b,'old_trace':ot,'new_trace':nt,'result_state':got[0],'head_displacement':got[1],'whole_tape_preserved':True})
    startup_raw=args.startup.read_bytes()
    if args.startup.suffix=='.gz':startup_raw=gzip.decompress(startup_raw)
    st=json.loads(startup_raw);assert st['steps']==95726 and len(st['trace'])==95726
    result=dense(n,0,st['steps'],st['trace']);assert result['state']==st['state'] and result['head']==st['head'] and result['one_cells']==st['one_cells']
    decoded=decode(result)
    for k in('gap','registers','spares'):assert decoded[k]==st[k]
    assert st['state']==84 and st['head']==-8 and decoded['gap']==1 and decoded['registers']==[4,0,0,0,0,0,0,0,0]
    assert decoded['spares']==[1]*40 and len(result['one_cells'])==95
    mapping={x:i for i,x in enumerate(sorted(q))};mapping[254]=215
    c={(mapping[x],b):(w,d,mapping[z])for(x,b),(w,d,z)in n.items()}
    if args.canonical is not None:
        literal_c,cs=read(args.canonical,215);assert literal_c==c and cs==mapping[0]
    cr=dense(c,mapping[0],st['steps']);assert cr['state']==mapping[84] and cr['head']==result['head'] and cr['one_cells']==result['one_cells']
    out={'status':'INDEPENDENT_DENSE_BLANK_AND_TWO_LOCAL_FOLDS_PASS','table_sha256':hashlib.sha256(args.table.read_bytes()).hexdigest(),'partial_selector_table_sha256':hashlib.sha256(args.partial.read_bytes()).hexdigest(),'working_states':215,'transition_rows':430,'graph_reachable_working_states':len(reachable),'deleted_from_public_partial216':[185],'added_states':[],'changed_retained_rows':sum(x['new']is not None for x in delta),'delta':delta,'folds':[first,second],'helper81':helper,'dense_blank':{**result,'steps':st['steps'],**decoded},'canonical_dense_blank':{'state':cr['state'],'head':cr['head'],'whole_tape_matches':True},'upstream_attribution':'Composes the public K216 Partial Selector and K216 Permuted Commands constructions; their separate ideas, tables, inherited proofs, and notices remain upstream work. This receipt independently checks the new composition.','scope':'All-tape proofs are only the explicitly unfolded local quotients and the 81-helper fragment. Dense startup is an exact finite fact. Full arbitrary-natural primitive runtime and source-command calibration are separate obligations.'}
    if args.canonical is not None:out['canonical_sha256']=hashlib.sha256(args.canonical.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k not in('delta','dense_blank','helper81')},indent=2))
    print('DENSE_BLANK', {k:v for k,v in out['dense_blank'].items()if k not in('one_cells','spares')})

if __name__=='__main__':main()
