#!/usr/bin/env python3
"""Check the exact tables and all local proof obligations for Detour242.

This is a relative machine proof checker with no extra input premise. It
derives by a structural induction that old states15,18,47,65 have a zero
immediately left, and that old27 always reads0, for every execution starting
in95 with arbitrary head and tape. No bounded trace or source-reachability
assumption is used. No new source-calibration theorem or Lean execution is
claimed by this script.

Whole-tape block identities below are symbolic. An unread exterior cell is
an independent formal atom, not a zero cell. Equality of normalized overlays
therefore establishes equality of entire tapes under every valuation of the
exterior. Translating head0 to any integer head is immediate.
"""
from pathlib import Path
import argparse,hashlib,json

BASE_SHA='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
NEW_SHA='c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
CANONICAL_SHA='ef8c07f372c76a73c021f51801f16f28f1e4ca5ead2d4ce6780c2a245a0db245'

def require(x,message):
    if not x:raise AssertionError(message)

def read_table(path):
    raw=path.read_bytes();table={};start=None
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):start=int(line.split()[-1])
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        require((q,b)not in table,'Duplicate row')
        require(b in(0,1)and w in(0,1)and d in('L','R'),'Invalid row')
        table[q,b]=(w,1 if d=='R'else-1,t)
    return raw,start,table

def run(table,q,known,steps):
    """Return symbolic full-configuration endpoint and literal row trace."""
    overlay={};head=0;trace=[]
    initial=lambda i:known.get(i,('initial_tape_cell',i))
    for unused in range(steps):
        read=overlay.get(head,initial(head))
        require(type(read)is int and read in(0,1),'Unspecified symbol inspected')
        key=q,read;trace.append(list(key));write,delta,q=table[key]
        if write==initial(head):overlay.pop(head,None)
        else:overlay[head]=write
        head+=delta
    return (q,head,tuple(sorted(overlay.items()))),trace

def main():
    here=Path(__file__).resolve().parents[1]
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,default=here/'reference/zfc_combined243_old.tm')
    ap.add_argument('--candidate',type=Path,default=here/'machine/zfc_detour242_old.tm')
    ap.add_argument('--canonical',type=Path,default=here/'machine/zfc_detour242.tm')
    ap.add_argument('--renumbering',type=Path,default=here/'machine/renumbering.json')
    ap.add_argument('--output',type=Path,default=here/'evidence/local-proof.json')
    args=ap.parse_args()
    ob,os,old=read_table(args.baseline);nb,ns,new=read_table(args.candidate)
    cb,cs,canonical=read_table(args.canonical)
    require(hashlib.sha256(ob).hexdigest()==BASE_SHA,'Wrong exact baseline')
    require(hashlib.sha256(nb).hexdigest()==NEW_SHA,'Wrong exact candidate')
    require(hashlib.sha256(cb).hexdigest()==CANONICAL_SHA,'Wrong canonical table')
    require(os==ns==95 and cs==0,'Unexpected start state')
    old_states={q for q,b in old};new_states={q for q,b in new}
    require(len(old_states)==243 and len(old)==486,'Wrong old count')
    require(len(new_states)==242 and len(new)==484,'Wrong new count')
    require(old_states-new_states=={27} and not new_states-old_states,'Wrong deletion')
    require(set(old)=={(q,b)for q in old_states for b in(0,1)},'Old table is partial')
    require(set(new)=={(q,b)for q in new_states for b in(0,1)},'New table is partial')
    require({t for w,d,t in new.values()}-new_states=={254},'Wrong halt target')
    require(all(t!=27 for w,d,t in new.values()),'Deleted state still targeted')
    expected={(q,b):(w,d,15 if t==27 else t)
              for(q,b),(w,d,t)in old.items()if q!=27}
    expected[15,0]=(0,-1,32)
    require(new==expected,'Candidate differs from the stated literal patch')
    changed={key for key in new if old[key]!=new[key]}
    require(changed=={(15,0),(18,0),(47,0),(65,0)},'Wrong changed rows')
    mapping=json.loads(args.renumbering.read_text())
    ren={int(k):v for k,v in mapping['old_to_canonical'].items()}
    require(ren[95]==0 and ren[254]==242,'Wrong canonical endpoints')
    require(set(ren)==new_states|{254}and set(ren.values())==set(range(243)),
            'Renumbering is not a bijection')
    require(canonical=={(ren[q],b):(w,d,ren[t])for(q,b),(w,d,t)in new.items()},
            'Canonical table does not match')

    left_zero_states={15,18,47,65}
    incoming_left_zero={t:[(q,b,w,d)for(q,b),(w,d,target)in old.items()if target==t]
                        for t in sorted(left_zero_states)}
    expected_incoming={15:[(11,0,0,1)],18:[(12,0,0,1),(148,0,0,1)],
                       47:[(33,0,0,1),(144,0,0,1),(167,0,0,1)],
                       65:[(51,0,0,1),(81,0,0,1)]}
    require(incoming_left_zero==expected_incoming,'Left-zero invariant predecessor changed')
    require(os not in left_zero_states|{27},'Initial invariant is not vacuous')
    require(all(w==0 and d==1 for incoming in incoming_left_zero.values()
                for q,b,w,d in incoming),'Left-zero target is not entered by0R')
    incoming27={(q,b)for(q,b),(w,d,t)in old.items()if t==27}
    require(incoming27=={(18,0),(47,0),(65,0)},'Wrong deleted-state incoming set')
    require(all(q in left_zero_states and old[q,b]==(0,-1,27)for q,b in incoming27),
            'Zero-read invariant predecessor changed')
    blocks=[]
    def block(name,q,known,m,n,target,head):
        a,ta=run(old,q,known,m);b,tb=run(new,q,known,n)
        require(a==b==(target,head,()),'Whole-tape block identity failed: '+name)
        blocks.append({'name':name,'entry_state':q,'known_initial_cells':known,
            'old_steps':m,'new_steps':n,'old_rows':ta,'new_rows':tb,
            'endpoint_state':target,'endpoint_head_offset':head,
            'whole_tape_unchanged':True,'outside_cells_arbitrary':True})
    block('original15 with current zero and left zero',15,{-1:0,0:0},1,3,21,1)
    block('original15 with current one',15,{-1:0,0:1},1,1,22,1)
    for q in(18,47,65):
        block('entry through old27 from'+str(q),q,{-1:0,0:0},2,2,32,-2)
    exceptional={(15,0)}|incoming27
    ordinary=[]
    for key,row in old.items():
        q,b=key
        if q==27 or key in exceptional:continue
        require(new[key]==row,'Nonexceptional row changed')
        require(row[2]!=27,'Ordinary row enters excluded comparison control')
        ordinary.append(list(key))
    require(len(ordinary)==480,'Wrong ordinary row census')
    # The stronger direct relation maps old27 to new15. It simulates every
    # old step individually, with a three-step clock only at old(15,0).
    fold=lambda q:15 if q==27 else q
    mapped_ordinary=[]
    for(q,b),(w,d,t)in old.items():
        if(q,b)in{(15,0),(27,1)}:continue
        require(new[fold(q),b]==(w,d,fold(t)),'Mapped single-step row failed')
        mapped_ordinary.append([q,b])
    require(len(mapped_ordinary)==484,'Wrong mapped ordinary row census')
    removed_old,removed_old_trace=run(old,27,{0:0},1)
    removed_new,removed_new_trace=run(new,15,{0:0},1)
    require(removed_old==removed_new==(32,-1,()),'Mapped removed-state block failed')
    result={'status':'PASS_UNCONDITIONAL_RELATIVE_MACHINE_PROOF','baseline_sha256':BASE_SHA,
        'candidate_old_sha256':NEW_SHA,'candidate_canonical_sha256':CANONICAL_SHA,
        'working_states':242,'binary_rows':484,'removed_state':27,
        'changed_retained_rows':[list(k)for k in sorted(changed)],
        'unchanged_retained_rows':480,'ordinary_single_step_rows':len(ordinary),
        'old_structural_invariant':{'initial_state':95,'left_zero_states':sorted(left_zero_states),
            'incoming_rows_to_left_zero_states':incoming_left_zero,
            'incoming_rows_to_old27':[list(k)for k in sorted(incoming27)],
            'argument':'All incoming rows to15,18,47,65 write0 and moveR. Every incoming row to27 movesL from18,47,65. Induction gives a zero left at those four states and a zero current cell at27.'},
        'blocks':blocks,'all_block_clocks_strictly_positive':True,
        'paired_control_excludes_old27':True,
        'stronger_direct_state_map':{'map':'f(27)=15; f(q)=q otherwise',
            'ordinary_rows':len(mapped_ordinary),'exceptional_slow_row':[15,0],
            'inadmissible_old_row':[27,1],
            'removed_state_block':{'old_entry_state':27,'new_entry_state':15,
                'known_initial_cells':{0:0},'old_rows':removed_old_trace,
                'new_rows':removed_new_trace,'endpoint_state':32,
                'endpoint_head_offset':-1,'whole_tape_unchanged':True},
            'old_clock':1,'new_clocks':[1,3],
            'exact_elapsed_time':'n old steps correspond to n+2*k new steps, where k counts old(15,0) in those n steps.'},
        'additional_input_premises':[],
        'conclusion':'For every head and tape, old243 and Detour242 have equivalent halting from shared start95. Blank input is included.',
        'scope':'Structural inductive invariant, exact finite symbolic whole-tape identities, and exhaustive table classification; unconditional relative ordinary proof, not a Lean theorem.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
