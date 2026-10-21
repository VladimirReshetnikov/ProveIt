#!/usr/bin/env python3
"""Independent four-case proof audit of the literal 400-to-69 fold.

No construction, compiler, source-language, or runtime module is imported.
The checked facts instantiate the accompanying ordinary mathematical proof.
This script is not a proof-assistant kernel.
"""
from pathlib import Path
import argparse, hashlib, json

OLD_SHA='34617022def75d88a4f357589d7a48f468d17b58c910947ed0738aa3c6a5760a'
NEW_SHA='c902a3c5e81176230a2213d631e2e691573c167fb03e9bdb09ef5c88154f3099'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def read(path, expected_hash):
    raw=path.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==expected_hash,'Incorrect literal input: '+str(path))
    rows={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        elif line and not line.startswith('#'):
            q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
            require((q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R'),'Malformed transition row')
            rows[q,b]=(w,1 if d=='R'else -1,z)
    states={q for q,b in rows}
    require(starts==[0] and 0 in states and 254 not in states,'Initial/halting convention')
    require(set(rows)=={(q,b)for q in states for b in(0,1)},'Missing row')
    require({z for w,d,z in rows.values()}-states=={254},'Unexpected target')
    return rows,states

def audit(old,new):
    oldq={q for q,b in old};newq={q for q,b in new}
    require(newq==oldq-{400} and len(oldq)==218 and len(newq)==217,'Wrong state deletion')
    phi=lambda q:69 if q==400 else q
    incoming=lambda q:[(key,act)for key,act in sorted(old.items())if act[2]==q]
    require(incoming(69)==[((53,1),(1,1,69))],'State69 marker premise')
    require(incoming(400)==[((224,0),(0,1,400))],'State400 marker premise')
    require(69!=0 and 400!=0,'Folded state cannot be initial')
    unchanged=0
    for (q,b),(w,d,z)in old.items():
        if q in(69,400):continue
        require(new[phi(q),b]==(w,d,phi(z)),'Unaccounted nonlocal mutation: '+str((q,b)))
        unchanged+=1
    cases=[]
    for role,marker in((69,1),(400,0)):
        for bit in(0,1):
            w,d,z=old[role,bit]
            require(w==bit and d==1,'Old branch does not preserve its scanned bit')
            initial={-1:marker,0:bit};tape=initial.copy();q,h=69,0;trace=[]
            for k in range(1,5):
                require(h in tape,'Candidate read outside two known cells')
                require(q!=254,'Unexpected interior halt')
                read_bit=tape[h];nw,nd,nq=new[q,read_bit]
                trace.append(dict(state=q,head=h,read=read_bit,write=nw,move=nd,next=nq))
                tape[h]=nw;h+=nd;q=nq
                if(q,h)==(phi(z),d):break
            else:raise ValueError('Expected local endpoint not reached')
            require(tape==initial,'Complete local tape differs at endpoint')
            require(len(trace)==(3 if bit==0 else 1),'Wrong local duration')
            cases.append(dict(old_state=role,marker=marker,scanned_bit=bit,old_duration=1,
                              new_duration=len(trace),endpoint_state=q,endpoint_head=h,
                              read_cells=sorted({t['head']for t in trace}),trace=trace))
    return dict(status='INDEPENDENT_LITERAL_FOUR_CASE_FOLD_PASS',old_working_states=218,
                new_working_states=217,unchanged_mapped_rows=unchanged,
                original_incoming_69=incoming(69),original_incoming_400=incoming(400),cases=cases,
                scope='All binary tapes and integer head positions starting in state0. '
                      'Predecessor writes supply the marker at every old visit to69 or400; '
                      'the four local cases read only cells-1 and0 and preserve them. '
                      'Every remaining row is an exact state-map copy. Thus each old '
                      'transition corresponds to1 or3 new transitions with identical '
                      'whole tape and head, and no interior halt. This is relative '
                      'halting equivalence to the supplied prefold218, not standalone '
                      'ZFC calibration or proof-assistant verification.')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--old',type=Path,required=True);p.add_argument('--new',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    old,_=read(a.old,OLD_SHA);new,_=read(a.new,NEW_SHA);out=audit(old,new)
    # A semantic negative control must fail because the initial row is mapped unchanged.
    corrupt=new.copy();corrupt[0,0]=(0,1,254)
    try:audit(old,corrupt)
    except ValueError as exc:out['negative_control']={'status':'REJECTED','reason':str(exc)}
    else:raise ValueError('Corrupt initial halt was accepted')
    out.update(old_sha256=OLD_SHA,new_sha256=NEW_SHA,
               checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(out['status'],out['new_working_states'],'states;',len(out['cases']),'exact local cases;',
          out['unchanged_mapped_rows'],'mapped rows; negative control rejected')
if __name__=='__main__':main()
