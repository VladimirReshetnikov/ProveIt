#!/usr/bin/env python3
"""Delete native state 211 using a two-cell predecessor invariant.

No source-layout/runtime module or saved verdict is imported.  The checker
reads both complete tables, proves the required predecessor predicates from
their complete incoming-edge inventories, and checks four finite paths with
arbitrary, unread tape exterior.  Explicit exceptions remain active under -O.

The theorem is a positive block simulation for every tape initially in
state 0.  It is ordinary executable mathematical evidence, not a proof-
assistant certificate for the inherited PA consistency calibration.
"""
import argparse, hashlib, json
from pathlib import Path

REMOVE, KEEP, HELPER, HALT = 211, 172, 214, 254

def need(ok, message):
    if not ok: raise ValueError(message)

def read(path):
    table, starts = {}, []
    for n,line in enumerate(Path(path).read_text(encoding='ascii').splitlines(),1):
        if line.startswith('#! start '): starts.append(int(line.split()[-1]))
        if not line or line.startswith('#'): continue
        fields=line.split();need(len(fields)==5, 'Malformed row '+str(n))
        q,b,w,d,z=fields
        q,b,w,z=map(int,(q,b,w,z))
        need((q,b) not in table and b in (0,1) and w in (0,1) and d in ('L','R'), 'Invalid transition')
        table[q,b]=(w,1 if d=='R' else -1,z)
    need(starts==[0],'Start declaration')
    validate(table)
    return table

def validate(table,halt=HALT):
    states={q for q,b in table}
    need(0 in states and halt not in states,'Start/halt domain')
    need(set(table)=={(q,b) for q in states for b in (0,1)},'Complete binary table')
    need(all(w in (0,1) and d in (-1,1) and (z in states or z==halt) for w,d,z in table.values()),'Target closure')
    seen={0};todo=[0]
    for q in todo:
        for b in (0,1):
            z=table[q,b][2]
            if z!=halt and z not in seen:seen.add(z);todo.append(z)
    need(seen==states,'Graph-unreachable working state')
    return states

def enc(table):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(table.items()))).encode('ascii')

def rho(q): return KEEP if q==REMOVE else q

def build(old):
    new={(q,b):(w,d,rho(z)) for (q,b),(w,d,z) in old.items() if q!=REMOVE}
    new[KEEP,0]=(0,-1,HELPER)
    return new

def incoming(t,q):
    return sorted((p,b,w,d) for (p,b),(w,d,z) in t.items() if z==q)

def predicates(old):
    # The two supplied U209 layouts exchange the roles of 163 and 216.
    s=old[HELPER,0][2]; t=old[HELPER,1][2]
    need(len({0,REMOVE,KEEP,HELPER,s,t,116,157,67,184,HALT})==11,'Distinct roles')
    required={
        (REMOVE,0):(0,1,157), (REMOVE,1):(1,1,184),
        (KEEP,0):(0,-1,67), (KEEP,1):(1,1,184),
        (HELPER,0):(0,1,s), (HELPER,1):(1,1,t),
        (s,0):(0,-1,REMOVE), (s,1):(1,1,REMOVE),
        (t,0):(0,1,157), (t,1):(1,1,116),
        (116,0):(0,1,KEEP), (157,0):(0,-1,67),
    }
    for key,value in required.items():need(old[key]==value,'Required row '+str(key))
    census={q:incoming(old,q) for q in (REMOVE,KEEP,116,s,HELPER)}
    need(census[REMOVE]==[(s,0,0,-1),(s,1,1,1)],'Complete entrances to211')
    need(census[KEEP]==[(116,0,0,1)],'Complete entrances to172')
    need(census[116] and all(w==1 and d==1 for p,b,w,d in census[116]),'Left tag of116')
    need(census[HELPER] and all(w==1 and d==1 for p,b,w,d in census[HELPER]),'Left tag of helper')
    need((HELPER,0,0,1) in census[s], 'Missing zero entrance to selector')
    need(all(d==1 and ((w==0 and (p,b)==(HELPER,0)) or w==1) for p,b,w,d in census[s]),'Unique zero entrance to selector')
    return s,t,census

def run(table,q,cells,ticks):
    tape=dict(cells);h=0;trace=[]
    for _ in range(ticks):
        need(q!=HALT and h in tape,'Read of opaque exterior or early halt')
        b=tape[h];w,d,z=table[q,b]
        trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
    return (q,h,tape),trace

def certify(old,new):
    a=validate(old);b=validate(new)
    need(b==a-{REMOVE} and len(b)==len(a)-1,'Exactly one state deleted')
    s,t,census=predicates(old)
    need(new[KEEP,0]==(0,-1,HELPER),'Replacement selector row')
    need(new[KEEP,1]==old[KEEP,1],'Shared read-one row')
    ordinary=0
    for (q,bit),(w,d,z) in old.items():
        if q not in (REMOVE,KEEP):
            need(new[q,bit]==(w,d,rho(z)),'Ordinary commuting row '+str((q,bit)))
            ordinary+=1
    cases=[(REMOVE,0,{-1:1,0:0},3), (REMOVE,1,{0:1},1),
           (KEEP,0,{-2:1,-1:0,0:0},7), (KEEP,1,{0:1},1)]
    paths=[]
    for q,bit,cells,ticks in cases:
        old_end,old_trace=run(old,q,cells,1)
        new_end,new_trace=run(new,rho(q),cells,ticks)
        need(new_end==(rho(old_end[0]),old_end[1],old_end[2]),'Finite path mismatch '+str((q,bit)))
        need(new_end[2]==cells,'Tape changed in a special block')
        paths.append(dict(old_state=q,read=bit,known_cells=cells,old_steps=1,new_steps=ticks,
                          old_trace=old_trace,new_trace=new_trace,exterior_unread=True,
                          endpoint_state=new_end[0],endpoint_head=new_end[1]))
    return dict(old_working_states=len(a),new_working_states=len(b),
                old_rows=len(old),new_rows=len(new),ordinary_rows=ordinary,
                changed_row=[KEEP,0,0,'L',HELPER],deleted_state=REMOVE,
                representative=KEEP,selector=s,continuation=t,
                complete_incoming=census,paths=paths,
                predicates=['old211 and scanned0 implies tape[-1]=1',
                            'old172 implies tape[-2]=1 and tape[-1]=0'],
                clock='Tchild = Tparent + 2*N(parent211/read0) + 6*N(parent172/read0)',
                clock_bound='Tparent <= Tchild <= 7*Tparent')

def negative_controls(old,new):
    s,t,census=predicates(old)
    tests=[]
    for name,which,key,act in [
        ('bad new selector direction','new',(KEEP,0),(0,1,HELPER)),
        ('bad new selector target','new',(KEEP,0),(0,-1,t)),
        ('bad new selector write','new',(KEEP,0),(1,-1,HELPER)),
        ('bad old172 predecessor tag','both',(116,0),(1,1,KEEP)),
        ('bad old116 predecessor tag','both',(t,1),(0,1,116)),
        ('bad helper predecessor tag','both',census[HELPER][0][:2],(0,1,HELPER)),
        ('extra zero entry to selector','both',next((p,b) for p,b,w,d in census[s] if w==1),(0,1,s)),
        ('bad helper read-zero branch','new',(t,0),(0,1,67)),
    ]:
        a,b=dict(old),dict(new)
        if which=='both':a[key]=act
        b[key]=(act[0],act[1],rho(act[2]))
        try:certify(a,b)
        except (ValueError,KeyError) as e:tests.append(dict(name=name,rejection=str(e)))
        else:raise ValueError('Accepted negative control: '+name)
    return tests

def main():
    global HELPER
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('parent',type=Path);ap.add_argument('--child',type=Path)
    ap.add_argument('--helper',type=int,default=214,help='Plain/Compatibility:214; Joint:217')
    ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    HELPER=a.helper
    old=read(a.parent);new=read(a.child) if a.child else build(old)
    result=certify(old,new)
    result['negative_controls']=negative_controls(old,new)
    a.output.mkdir(parents=True,exist_ok=True)
    n=result['new_working_states'];raw=enc(new)
    (a.output/f'u{n}.native.tm').write_bytes(raw)
    rename={q:i for i,q in enumerate(sorted({q for q,b in new}))};rename[HALT]=n
    dense={(rename[q],bit):(w,d,rename[z]) for (q,bit),(w,d,z) in new.items()}
    validate(dense,n);draw=enc(dense)
    (a.output/f'u{n}.tm').write_bytes(draw)
    (a.output/'state_map.json').write_text(json.dumps({'native_to_dense':rename,'native_halt':HALT,'dense_halt':n},indent=2)+'\n')
    result.update(status='FINITE_LOCAL_TWO_CELL_FOLD_PASS',parent_sha256=hashlib.sha256(a.parent.read_bytes()).hexdigest(),
                  native_sha256=hashlib.sha256(raw).hexdigest(),dense_sha256=hashlib.sha256(draw).hexdigest(),
                  scope='Positive block simulation for every common tape initially in state0. Ordinary mathematical finite verification; inherited source and PA calibration are separate.')
    (a.output/'fold211_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('paths','complete_incoming','negative_controls')},indent=2))

if __name__=='__main__':main()
