#!/usr/bin/env python3
"""Portable literal checker for the GC215 conditional decoder merge.

Usage:
  python check_decoder_merge.py --parent SAFE216 --table GC215 --out OUTPUT

Uses the Python standard library only.  The source compiler and arbitrary-
natural primitive runtime are separate obligations.  This checker proves the
finite hypotheses of the all-tape simulation lemma in the accompanying report.
"""
import argparse,hashlib,json
from pathlib import Path

PARENT_SHA='f0b7ae5e41fb6445afd1bf5e1618f6dd059c1dacbce47d3f81086ef69da33629'
TABLE_SHA='a5d8dfeb92a6ae843692c65b5eaf69b845b08b48d65dc011ba8a457e4faec67d'
def need(test,message):
    if not test:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def read(data):
    rows={};starts=[]
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need(b in(0,1)and w in(0,1)and d in('L','R')and(q,b)not in rows,'Invalid native row')
        rows[q,b]=(w,1 if d=='R'else-1,z)
    need(starts==[0],'Exactly one start0 declaration required')
    states={q for q,b in rows}
    need(set(rows)=={(q,b)for q in states for b in(0,1)},'Partial table')
    halts={z for w,d,z in rows.values()}-states
    need(len(halts)==1,'Exactly one separate halt control required')
    return rows,states,halts.pop()
def serialize(T):
    return ('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'
            for(q,b),(w,d,z)in sorted(T.items()))).encode('ascii')
def phi(q):return 129 if q==310 else q
def execute(T,q,b,left,steps):
    cells={-1:left,0:b};head=0;trace=[]
    for _ in range(steps):
        need(head in cells,'A local proof read an unconstrained exterior cell')
        bit=cells[head];w,d,z=T[q,bit]
        trace.append([q,head,bit,w,d,z]);cells[head]=w;head+=d;q=z
    return q,head,cells,trace
def reachable(T,halt):
    reached={0};todo=[0]
    for q in todo:
        for b in(0,1):
            z=T[q,b][2]
            if z!=halt and z not in reached:reached.add(z);todo.append(z)
    return reached
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent',type=Path,required=True)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    parent_raw=args.parent.read_bytes();native_raw=args.table.read_bytes()
    need(sha(parent_raw)==PARENT_SHA,'Corrected parent216 hash mismatch')
    need(sha(native_raw)==TABLE_SHA,'Final native215 hash mismatch')
    T,oldstates,oldhalt=read(parent_raw);N,newstates,newhalt=read(native_raw)
    need(len(oldstates)==216 and len(newstates)==215 and oldhalt==newhalt==254,'State census')
    need(oldstates-newstates=={310}and not newstates-oldstates,'Wrong deleted state')
    need(reachable(T,254)==oldstates and reachable(N,254)==newstates,'Graph-unreachable working state')
    expected={k:(w,d,phi(z))for k,(w,d,z)in T.items()if k[0]!=310}
    expected[129,1]=(1,-1,216)
    need(N==expected,'Final table is not the exact prescribed merge')
    incoming129={k:v for k,v in T.items()if v[2]==129}
    incoming310={k:v for k,v in T.items()if v[2]==310}
    need(incoming129=={(211,1):(1,1,129)},'Old129 origin-marker premise')
    need(incoming310=={(312,0):(0,1,310)},'Old310 origin-marker premise')
    need(T[129,0]==T[310,0]==N[129,0]==(0,1,154),'Common read0 row')
    need(T[129,1]==(1,1,189)and T[310,1]==(1,1,86),'Old read1 rows')
    helpers={(216,0):(0,1,157),(216,1):(1,1,178),(157,1):(1,-1,148),
             (148,0):(0,1,186),(186,1):(1,1,86),(178,1):(1,1,189)}
    need(all(T[k]==v and N[k]==v for k,v in helpers.items()),'A helper row changed')
    blocks=[]
    for oldq,left in[(129,1),(310,0)]:
        for bit in(0,1):
            steps=1 if bit==0 else(3 if left==1 else 5)
            oq,oh,ot,otrace=execute(T,oldq,bit,left,1)
            nq,nh,nt,ntrace=execute(N,129,bit,left,steps)
            need((nq,nh,nt)==(phi(oq),oh,ot),'Local macro does not simulate old step')
            need(nt=={-1:left,0:bit},'Local macro changed tape')
            blocks.append(dict(old_state=oldq,left_marker=left,read=bit,old_steps=1,new_steps=steps,
                               target=nq,head_delta=nh,old_trace=otrace,new_trace=ntrace))
    dense_map={q:i for i,q in enumerate(sorted(newstates))};dense_map[254]=215
    need(dense_map[0]==0 and len(set(dense_map.values()))==216,'Dense map is not bijective')
    dense={(dense_map[q],b):(w,d,dense_map[z])for(q,b),(w,d,z)in N.items()}
    dense_raw=serialize(dense);D,ds,dh=read(dense_raw)
    need(ds==set(range(215))and dh==215 and D==dense,'Dense serialization failed')
    need(reachable(D,215)==ds,'Dense graph reachability failed')
    (args.out/'GC215.tm').write_bytes(dense_raw)
    (args.out/'native-to-dense.json').write_text(json.dumps(dense_map,indent=2,sort_keys=True)+'\n')
    receipt=dict(status='LITERAL_DECODER_MERGE_AND_DENSE_BIJECTION_PASS',
        parent_sha256=sha(parent_raw),native_sha256=sha(native_raw),dense_sha256=sha(dense_raw),
        working_states=215,rows=430,halt_native=254,halt_dense=215,
        dispatcher_native=84,dispatcher_dense=dense_map[84],deleted_state=310,kept_state=129,
        graph_reachable_states=215,blocks=blocks,helper_rows=[list(k)+list(v)for k,v in sorted(helpers.items())],
        incoming_old129=[list(k)+list(v)for k,v in incoming129.items()],
        incoming_old310=[list(k)+list(v)for k,v in incoming310.items()],
        scope='All initial binary tapes and head positions, starting control0. Not arbitrary old control310 with an unconstrained origin marker.',
        induction='Old reachable129 has left marker1; old reachable310 has left marker0. Map310 to129 and retain tape/head. The four finite positive blocks simulate the folded states; all other rows commute with the map in one step. Block lengths are between1 and5, so finite halting and infinite execution are preserved in both directions.',
        checker_sha256=sha(Path(__file__).read_bytes()),
        separate_obligations=['all-natural primitive runtime','exact blank startup','source program semantics','calculus calibration'])
    (args.out/'decoder-merge.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k not in('blocks','induction')},indent=2))
if __name__=='__main__':main()
