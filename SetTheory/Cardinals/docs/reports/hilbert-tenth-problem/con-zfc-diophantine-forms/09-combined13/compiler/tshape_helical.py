#!/usr/bin/env python3
"""Four-site local relation equivalent globally to 06-blank67's relation.

Tuples are [left, center, right, following]. All constants and the completed
machine table are imported from the pinned blank-helical construction.
This module is a derivative compiler experiment, not a formal certificate.
"""
from pathlib import Path
import argparse
import json
import blank_helical as b
from verify_k215 import parse_tm, require

START = (b.L,b.Q,b.R,b.normal(1))
EXCLUDED = (b.V,b.H,b.V,b.Q)

def local_valid(window, table):
    if len(window) != 4 or any(type(x) is not int or not 0 <= x < b.ALPHABET_SIZE for x in window):
        return False
    left, center, right, following = [b.DECODED[x] for x in window]
    v,h,payload,phase = center
    if v != following[0] or (v and right[0]) or (h and following[1]):
        return False
    if not v and not right[0] and h != right[1]:
        return False
    # This is the original initialization-presence test translated one row.
    if not following[0] and not following[1]:
        if (following[3] is not None) != bool(h):
            return False
    if v or h:
        return True
    if phase is not None:
        if (left[0] and phase != b.L) or (right[0] and phase != b.R):
            return False
        if not right[0] and (phase,right[3]) not in b.PHASE_PAIRS:
            return False
    symbol,state=payload
    if following[1] and state is not None and state != b.HALT:
        return False
    if state is not None:
        move=table[state,symbol][2]
        if (move == -1 and left[0]) or (move == 1 and right[0]):
            return False
    if not following[1]:
        if (not left[0] and left[2] is None) or (not right[0] and right[2] is None):
            return False
        expected=b.next_payload((0,None) if left[0] else left[2], payload,
                                (0,None) if right[0] else right[2], table)
        if expected is None or following[2] != expected:
            return False
    return True

def overlap(center, right, following):
    return (center[2] == right[1] and center[1] == right[0]
            and center[3] == following[1])

def direct_center_count(center,table):
    v,h,payload,phase=b.DECODED[center]
    total=0
    for left in range(439):
        lt=b.DECODED[left]
        for right in range(439):
            rt=b.DECODED[right]
            candidates = [b.V] if v else [b.L,b.Q,b.R] if h else [b.H]
            if not v and not h and (lt[0] or lt[2] is not None) and (rt[0] or rt[2] is not None):
                expected=b.next_payload((0,None) if lt[0] else lt[2],payload,
                                        (0,None) if rt[0] else rt[2],table)
                if expected is not None:
                    candidates.append(b.normal(*expected))
            for following in candidates:
                total += local_valid((left,center,right,following),table)
    return total

def verify_semantics(table):
    controls=[]
    first=dict(table)
    first[93,0]=b.HALT,0,0
    controls.append(first)
    second=dict(table)
    second[93,0]=2,1,-1
    second[2,1]=3,0,-1
    second[3,0]=b.HALT,1,1
    controls.append(second)
    presentations=windows=mutants=0
    def projected(blocks):
        return [tuple(w[j] for j in (3,4,5,7)) for w in blocks]
    for control in controls:
        history=b.simulate(control,20)
        require(history[-1][2]==b.HALT,'Toy machine did not halt')
        width0=max(1,-min(h for _,h,_ in history))+max(1,max(h for _,h,_ in history))+2
        for dw in range(4):
            for dh in range(4):
                width=width0+dw
                grid,x0=b.strip(history,width,len(history)+1+dh)
                word=b.cyclic(grid,x0)
                original=b.lift(word,width)
                blocks=projected(original)
                require(all(b.local_valid(w,control) for w in original),'Bad old tableau')
                require(all(local_valid(w,control) for w in blocks),'Bad translated tableau')
                require(all(overlap(blocks[i],blocks[(i-1)%len(word)],blocks[(i-width)%len(word)])
                            for i in range(len(word))),'Four-site overlap')
                require(blocks[0]==START and blocks.count(START)==1,'Canonical Start')
                require(EXCLUDED not in blocks,'Excluded block in canonical presentation')
                presentations+=1;windows+=len(word)
                # Relocating one initialization test must preserve whole-plane
                # validity on arbitrary mutations too, not merely accepting fixtures.
                for pos in range(len(word)):
                    for symbol in (0,1,b.V,b.H,b.L,b.Q,b.R,b.normal(0,b.HALT)):
                        changed=word[:]
                        changed[pos]=symbol
                        old=b.lift(changed,width)
                        new=projected(old)
                        require(all(b.local_valid(w,control) for w in old)==
                                all(local_valid(w,control) for w in new),'Translated rule mismatch')
                        mutants+=1
    return dict(toy_presentations=presentations,valid_windows=windows,
                single_cell_mutated_periodic_planes=mutants,
                scope='Finite implementation checks; universal equivalence proved by translating one local conjunct.')

def verify(rows, direct=True):
    table=b.table_from_rows(rows)
    require(local_valid(START,table),"Start not locally valid")
    require(local_valid(EXCLUDED,table),"Excluded tuple not locally valid")
    # At E's successor Q, propagated left V contradicts its initialization rule.
    for right in range(439):
        for following in (b.H,b.normal(0),b.normal(1)):
            require(not local_valid((b.V,b.Q,right,following),table),"Excluded witness extends")
    li=sum(d == 1 for _,_,_,d,_ in rows)+1
    ri=sum(d == -1 for _,_,_,d,_ in rows)
    ln,rn=438-li,438-ri
    boundary=439*438
    internal=ln*rn+li*rn+ri*ln
    categories=[]
    def add(name,center,multiplicity,value):
        got=direct_center_count(center,table) if direct else None
        require(not direct or got==value,f"{name}: {got} != {value}")
        categories.append(dict(name=name,representative=center,multiplicity=multiplicity,
                               each=value,direct=got,subtotal=multiplicity*value))
    add("V",b.V,1,439*438)
    add("H",b.H,1,6*439)
    for sym in (0,1):
        add(f"headless-{sym}",b.normal(sym),1,boundary+internal)
        add(f"halt-{sym}",b.normal(sym,215),1,boundary+ln*rn)
    for write in (0,1):
        for direction in (-1,1):
            actions=[x for x in rows if x[2]==write and x[3]==direction]
            q,symbol,*_=actions[0]
            l,r=ln-(direction == -1),rn-(direction == 1)
            add(f"write{write}-move{direction}",b.normal(symbol,q),len(actions),l*r+li*r+ri*l)
    add("L",b.L,1,2*439+2*(ln+li))
    add("Q",b.Q,1,437)
    add("R",b.R,1,2*438+2*(ln-1+li))
    require(sum(x['multiplicity'] for x in categories)==439,"Partition")
    count=sum(x['subtotal'] for x in categories)
    require(count==71356645,"Cardinality")
    return dict(status="PASS",alphabet_size=439,windows=count,
                categories=categories,all_left_right_pairs_each_center_class=direct,
                semantic_checks=verify_semantics(table),
                complete_giant_window_list_materialized=False)

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--tm',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--formula-only',action='store_true')
    args=ap.parse_args()
    result=verify(parse_tm(args.tm.read_bytes()),not args.formula_only)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
