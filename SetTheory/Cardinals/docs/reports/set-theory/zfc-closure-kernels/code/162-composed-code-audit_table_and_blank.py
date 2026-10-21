#!/usr/bin/env python3
"""Independent, standalone census/isomorphism/blank-prefix audit for exact K215.

Usage:
  python3 -B audit_table_and_blank.py --native NATIVE --canonical CANONICAL \
      --mapping MAPPING_JSON --output RECEIPT_JSON [--trace TRACE_JSONL_GZ]

The parser, dense/sparse simulations, direct expected-frame constructor and
canonicalization checker do not import the compiler or symbolic runtime.
Only the Python standard library is required. This is a finite blank-prefix
and exact graph-isomorphism certificate; foundational calibration and the
unbounded primitive simulation remain separate obligations.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,struct

NATIVE_SHA='03739f080d023166773bc14e7e3a4d8157f81d44c28cd30fef46066b37cf3748'
CANONICAL_SHA='fd9de5a9702c6193350952ca85a43f65d288b20f234b7582549b6aaa7a5ce703'
MAPPING_SHA='5971896ea1be8b94675a49d0324b0cc5529e626bb059379f6d221077cae1ac86'
TRACE_GZIP_SHA='c2a946b08c8bb2df17952febce40071f486e165022c480e5c74dfb92b7069e13'
TRAJECTORY_SHA='2f7ff6f0deac8aa9377170b44a192862ca45027991cfae63856efc3470f1cdcb'
STEPS=95726
REGISTERS=[4,0,0,0,0,0,0,0,0]
SPARES=[1]*40
PHY=(6,2,0,4,3,7,8,5,1)

def need(ok,message):
    if not ok:raise ValueError(message)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def parse(path,halt):
    table={};starts=[];declared_halts=[]
    for lineno,line in enumerate(path.read_text().splitlines(),1):
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if line.startswith('#! halt '):declared_halts.append(int(line[8:]));continue
        if not line or line.startswith('#'):continue
        fields=line.split();need(len(fields)==5,f'Bad row at {lineno}')
        q,b,w,d,z=fields;q,b,w,z=map(int,(q,b,w,z))
        need(q>=0 and z>=0 and b in(0,1) and w in(0,1) and d in('L','R'),'Bad transition')
        need((q,b)not in table,'Duplicate transition')
        table[q,b]=(w,-1 if d=='L'else 1,z)
    states={q for q,b in table}
    need(starts==[0]and all(h==halt for h in declared_halts),'Wrong start/halt declaration')
    need(len(states)==215 and len(table)==430 and halt not in states,'Incorrect census')
    need(set(table)=={(q,b)for q in states for b in(0,1)},'Partial table')
    need({z for w,d,z in table.values()}-states=={halt},'Unexpected terminal state')
    reached={0};work=[0]
    while work:
        q=work.pop()
        for b in(0,1):
            z=table[q,b][2]
            if z in states and z not in reached:reached.add(z);work.append(z)
    need(reached==states,'Working states are not all graph reachable')
    return table,states

def row_isomorphism(native,canonical,forward):
    return {(forward[q],b):(w,d,forward[z])for(q,b),(w,d,z)in native.items()}==canonical

def expected_frame():
    physical=[None]*9
    for i,j in enumerate(PHY):physical[j]=REGISTERS[i]
    head=-8;header=head+64+1;ones={head-1,header};p=header+1
    for value in physical+SPARES:
        need(value>=0,'Negative natural register')
        p+=1;ones.update(range(p,p+value+1));p+=value+1
    need(header==57 and len(ones)==95 and len(SPARES)==40,'Expected frame constants')
    return ones,physical

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--native',type=Path,required=True)
    ap.add_argument('--canonical',type=Path,required=True)
    ap.add_argument('--mapping',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--trace',type=Path)
    a=ap.parse_args()
    need(sha(a.native)==NATIVE_SHA,'Wrong native bytes')
    need(sha(a.canonical)==CANONICAL_SHA,'Wrong canonical bytes')
    need(sha(a.mapping)==MAPPING_SHA,'Wrong mapping bytes')
    native,nstates=parse(a.native,254);canonical,cstates=parse(a.canonical,215)
    need(cstates==set(range(215)),'Canonical working labels are not 0..214')
    mapping=json.loads(a.mapping.read_text())
    forward={int(q):z for q,z in mapping['native_to_canonical'].items()}
    reverse={int(q):z for q,z in mapping['canonical_to_native'].items()}
    need(set(forward)==nstates|{254} and set(forward.values())==set(range(216)),'Not a bijection')
    need(reverse=={z:q for q,z in forward.items()},'Maps are not inverse')
    need(forward[0]==0 and forward[84]==83 and forward[254]==215,'Wrong distinguished states')
    need(mapping['native_sha256']==NATIVE_SHA and mapping['canonical_sha256']==CANONICAL_SHA,'Mapping byte identities')
    need(row_isomorphism(native,canonical,forward),'A transition does not commute with the relabelling')
    corrupt=canonical.copy();corrupt[0,0]=(1,1,215)
    need(not row_isomorphism(native,corrupt,forward),'Negative-control corrupted halt accepted')
    trace_stream=None
    if a.trace:
        need(sha(a.trace)==TRACE_GZIP_SHA,'Wrong compressed startup trace')
        trace_stream=gzip.open(a.trace,'rt',encoding='ascii')
    # The native machine uses a sparse tape; the canonical machine independently
    # reads, writes and moves on its dense tape. Both begin on complete blank.
    ones=set();dense=bytearray(400001);origin=200000
    nq=nh=cq=ch=0;low=high=0;used=set();trajectory=hashlib.sha256()
    try:
        for tick in range(STEPS):
            need(0<=ch+origin<len(dense),'Dense tape boundary reached')
            nb=int(nh in ones);cb=dense[ch+origin]
            need((nq,nb)in native and(cq,cb)in canonical,'Premature halt or undefined row')
            nw,nd,nz=native[nq,nb];cw,cd,cz=canonical[cq,cb]
            need(cq==forward[nq] and ch==nh and cb==nb,'Configurations diverge')
            need((cw,cd,cz)==(nw,nd,forward[nz]),'Runtime transitions diverge')
            if trace_stream:
                line=trace_stream.readline();need(bool(line),'Compressed trace ends early')
                need(json.loads(line)==[nq,nh,nb,nw,nd,nz],f'Trace mismatch at step {tick}')
            used.add((nq,nb))
            trajectory.update(struct.pack('>qqbbbbq',tick,nh,nb,nw,nd,0,nq)+struct.pack('>q',nz))
            if nw:ones.add(nh)
            else:ones.discard(nh)
            dense[ch+origin]=cw
            nq=nz;nh+=nd;cq=cz;ch+=cd
            low=min(low,nh);high=max(high,nh)
        if trace_stream:need(trace_stream.readline()=='','Compressed trace has extra rows')
    finally:
        if trace_stream:trace_stream.close()
    expected,physical=expected_frame()
    need((nq,nh,cq,ch)==(84,-8,83,-8),'Wrong endpoint control')
    need(ones==expected,'Sparse tape differs from complete expected frame')
    dense_ones={i-origin for i,b in enumerate(dense)if b}
    need(dense_ones==expected,'Dense tape differs from complete expected frame')
    need((low,high)==(-18,199),'Unexpected visited head interval')
    need(trajectory.hexdigest()==TRAJECTORY_SHA,'Wrong exact startup trajectory')
    need(all(x not in ones for x in range(-8,57)),'Root program-counter region is not all zero')
    need(sha(a.native)==NATIVE_SHA and sha(a.canonical)==CANONICAL_SHA and sha(a.mapping)==MAPPING_SHA,'Inputs changed during audit')
    receipt=dict(status='INDEPENDENT_K215_TABLE_AND_BLANK_PASS',
        native_sha256=NATIVE_SHA,canonical_sha256=CANONICAL_SHA,mapping_sha256=MAPPING_SHA,
        checker_sha256=sha(Path(__file__)),working_states=215,rows=430,
        graph_reachable_working_states=215,canonical_working_labels=[0,214],
        native_halt=254,canonical_halt=215,start_state=0,
        exact_inverse_mapping=True,all430_rows_commute=True,
        negative_control='Canonical initial transition redirected to halt was rejected',
        startup_steps=STEPS,native_final_state=84,canonical_final_state=83,final_head=-8,
        root_program_counter_empty=True,header=57,gap_extra=1,
        registers=REGISTERS,physical_registers=physical,spares=SPARES,
        spare_count=len(SPARES),whole_tape_one_cells=sorted(expected),one_cell_count=len(expected),
        visited_head_interval=[low,high],startup_visited_rows=len(used),
        trajectory_sha256=TRAJECTORY_SHA,
        compressed_trace_checked=bool(a.trace),compressed_trace_sha256=TRACE_GZIP_SHA if a.trace else None,
        scope='Exact arbitrary-tape isomorphism follows from the checked bijection and every transition row. Finite blank startup is checked by separate sparse/native and dense/canonical executions at every step, optional literal trace replay, and complete tape equality with a direct frame construction. All exterior cells remain zero since no head leaves the verified finite interval. Source calibration and unbounded primitive runtime are separate obligations.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k not in('spares','whole_tape_one_cells')},indent=2))
if __name__=='__main__':main()
