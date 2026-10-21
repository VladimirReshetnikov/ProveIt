#!/usr/bin/env python3
"""Independent finite-table, relabelling, and whole-blank-tape audit.

No constructor, decoder, or symbolic runtime implementation is imported.
This verifies the finite startup and presentation, not consistency calibration.
"""
import argparse,hashlib,json
from pathlib import Path

def need(c,m):
    if not c: raise ValueError(m)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
    rows={};start=None
    for line in p.read_text(encoding='utf-8').splitlines():
        if not line.strip():continue
        if line.startswith('#'):
            if line.startswith('#! start '):start=int(line.split()[-1])
            continue
        a=line.split();need(len(a)==5,'row width')
        q,b,w,d,z=int(a[0]),int(a[1]),int(a[2]),a[3],int(a[4])
        need(b in (0,1) and w in (0,1) and d in ('L','R'),'alphabet and move')
        need((q,b)not in rows,'duplicate row')
        rows[q,b]=(w,-1 if d=='L' else 1,z)
    need(start==0,'blank-start convention')
    working={q for q,b in rows};targets={z for w,d,z in rows.values()}
    need(set(rows)=={(q,b)for q in working for b in(0,1)},'total working rows')
    need(len(working)==217 and len(rows)==434,'state count')
    halts=targets-working;need(len(halts)==1,'unique halt label')
    halt=next(iter(halts));seen={0};front=[0]
    for q in front:
        for b in(0,1):
            z=rows[q,b][2]
            if z!=halt and z not in seen:seen.add(z);front.append(z)
    need(seen==working,'graph reachability')
    return rows,halt,working

def sparse(rows,halt,n,trace=None):
    state=head=0;ones=set();lo=hi=0;used=set()
    if trace is not None:need(len(trace)==n,'trace length')
    trace_digest=hashlib.sha256()
    for tick in range(n):
        need(state!=halt,'premature halt')
        b=int(head in ones);w,d,z=rows[state,b];used.add((state,b))
        event=[state,head,b,w,d,z]
        if trace is not None:need(trace[tick]==event,f'stored trace row {tick}')
        trace_digest.update((','.join(map(str,event))+'\n').encode('ascii'))
        if w:ones.add(head)
        else:ones.discard(head)
        state=z;head+=d;lo=min(lo,head);hi=max(hi,head)
    return state,head,ones,lo,hi,used,trace_digest.hexdigest()

def dense(rows,halt,n):
    # Cell >=0 in positive; cell -k in negative[k-1].
    positive=bytearray(1);negative=bytearray();q=h=0
    for tick in range(n):
        need(q!=halt,'premature dense halt')
        a,j=(positive,h)if h>=0 else(negative,-h-1)
        if j==len(a):a.append(0)
        need(j<len(a),'dense adjacency')
        row=rows[q,int(a[j])];a[j]=row[0];h+=row[1];q=row[2]
    support={j for j,x in enumerate(positive)if x}|{-j-1 for j,x in enumerate(negative)if x}
    return q,h,support,len(positive),len(negative)

def encode_frame(h,gap,registers,spares):
    physical=[None]*9
    for logical,physical_slot in enumerate((6,2,0,4,3,7,8,5,1)):physical[physical_slot]=registers[logical]
    out={h-1,h+64+gap};at=h+65+gap
    for n in physical+spares:
        need(type(n)is int and n>=0,'unary value')
        out.update(range(at+1,at+n+2));at+=n+2
    return out

def main():
    p=argparse.ArgumentParser();p.add_argument('--directory',type=Path,required=True);p.add_argument('--canonical',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    N=a.directory/'k217.native.tm';J=a.directory/'validation/startup.json';S=a.directory/'sites217.json'
    rows,halt,working=load(N);need(halt==254,'native halt')
    receipt=json.loads(J.read_text()) if J.exists() else {'steps':312617,'registers':[3,0,0,0,3,0,0,0,0],'spares':[1]*130,'gap':80}
    need(receipt['steps']==312617,'agreed startup checkpoint')
    q,h,O,lo,hi,used,trace_sha=sparse(rows,halt,receipt['steps'],receipt.get('trace'))
    need(q==84 and h==-5,'native endpoint')
    expected=encode_frame(-5,80,[3,0,0,0,3,0,0,0,0],[1]*130)
    need(len(expected)==277 and O==expected,'complete frame including zero exterior')
    if 'one_cells' in receipt:need(O==set(receipt['one_cells']) and len(receipt['one_cells'])==277,'receipt support')
    need(receipt['registers']==[3,0,0,0,3,0,0,0,0] and receipt['spares']==[1]*130 and receipt['gap']==80,'receipt fields')
    dq,dh,DO,np,nn=dense(rows,halt,receipt['steps']);need((dq,dh,DO)==(q,h,O),'dense/sparse agreement')
    sites=json.loads(S.read_text());need(len(sites)==4751,'source occurrence count')
    need(sites[0][1:]==['CD',8] and set(sites[0][0])<={'0'},'root code is all zeros for first instruction')
    need(not any(h<=x<h+64 for x in O),'entire control field clear')
    result={'status':'INDEPENDENT_FINITE_STARTUP_AND_TABLE_PASS','native_sha256':digest(N),'source_sha256':digest(S),'working_states':217,'rows':434,'native_halt':halt,'all_states_graph_reachable':True,'steps':receipt['steps'],'native_state':q,'head':h,'header':139,'gap':80,'logical_registers':receipt['registers'],'spare_count':130,'spare_value':1,'one_count':277,'complete_support':sorted(O),'visited_interval':[lo,hi],'dense_positive_cells':np,'dense_negative_cells':nn,'startup_transitions_independently_computed':receipt['steps'],'trace_rows_independently_replayed':len(receipt.get('trace',[])),'trace_sha256_csv_rows':trace_sha,'startup_rows_used':len(used),'source_occurrences':len(sites),'scope':'Independent finite startup and complete-tape equality only. Consistency calibration and unbounded primitive contracts are separate.'}
    if a.canonical:
        C=a.canonical;cr,ch,cw=load(C);need(cw==set(range(217)) and ch==217,'canonical labels')
        mapping={0:0,halt:ch};reverse={0:0,ch:halt};todo=[0]
        for old in todo:
            for b in(0,1):
                ow,od,oz=rows[old,b];nw,nd,nz=cr[mapping[old],b]
                need((ow,od)==(nw,nd),'relabel preserves write/move')
                if oz not in mapping:
                    need(nz not in reverse,'relabel injectivity');mapping[oz]=nz;reverse[nz]=oz
                    if oz!=halt:todo.append(oz)
                need(mapping[oz]==nz,'relabel target')
        need(set(mapping)==working|{halt} and set(mapping.values())==cw|{ch},'relabel total bijection')
        cq,chead,CO,_,_=dense(cr,ch,receipt['steps']);need((cq,chead,CO)==(mapping[q],h,O),'canonical dense startup')
        result.update(canonical_sha256=digest(C),canonical_halt=ch,canonical_dispatcher=mapping[84],canonical_state=cq,canonical_relabel_map={str(k):v for k,v in sorted(mapping.items())},canonical_blank_startup_pass=True)
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k not in('complete_support','canonical_relabel_map')},indent=2))
if __name__=='__main__':main()
