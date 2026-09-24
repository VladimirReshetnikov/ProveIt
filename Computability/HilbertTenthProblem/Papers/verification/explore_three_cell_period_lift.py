#!/usr/bin/env python3
"""Exact-period three-cell block lift and fixed marked-TM window."""
from itertools import product
from pathlib import Path
import json
import random
import sys

import explore_marked_periodic_tm_padding as tableau
import explore_four_cell_period_lift as previous

OUT=Path(__file__).with_suffix('.json')
BLOCKS=tuple(product((0,1),repeat=9))


def window(grid,x,t):
    height,width=len(grid),len(grid[0])
    return tuple(grid[(t+dt)%height][(x+dx)%width]
                 for dt in (-1,0,1) for dx in (-1,0,1))


def lift(grid):
    return [[window(grid,x,t) for x in range(len(grid[0]))] for t in range(len(grid))]


def project(blocks):
    return [[block[4] for block in row] for row in blocks]


def horizontal(center,right):
    return all(center[3*v+u+1]==right[3*v+u] for v in range(3) for u in range(2))


def vertical(center,nxt):
    return center[3:]==nxt[:6]


def three_valid(center,right,nxt,predicate):
    return (predicate(center) and predicate(right) and predicate(nxt)
            and horizontal(center,right) and vertical(center,nxt))


def old_valid(grid,predicate):
    return all(predicate(window(grid,x,t)) for t in range(len(grid)) for x in range(len(grid[0])))


def new_valid(grid,predicate):
    height,width=len(grid),len(grid[0])
    return all(three_valid(grid[t][x],grid[t][(x+1)%width],grid[(t+1)%height][x],predicate)
               for t in range(height) for x in range(width))


def verify_local():
    pairs=hpairs=vpairs=triples=0
    rights={};nexts={}
    for center in BLOCKS:
        rights[center]=[];nexts[center]=[]
        for other in BLOCKS:
            href=all(center[3*v+u]==other[3*v+u-1] for v in range(3) for u in (1,2))
            vref=all(center[3*v+u]==other[3*(v-1)+u] for v in (1,2) for u in range(3))
            assert horizontal(center,other)==href and vertical(center,other)==vref
            if href:rights[center].append(other);hpairs+=1
            if vref:nexts[center].append(other);vpairs+=1
            pairs+=1
        assert len(rights[center])==len(nexts[center])==8
        for right,nxt in product(rights[center],nexts[center]):
            assert three_valid(center,right,nxt,lambda w:True)
            assert not three_valid(center,right,nxt,lambda w:False)
            for slot in (0,4,8):
                predicate=lambda w,slot=slot:bool(w[slot])
                assert three_valid(center,right,nxt,predicate)==all(predicate(w) for w in (center,right,nxt))
            triples+=1
    assert pairs==262144 and hpairs==vpairs==4096 and triples==32768
    return dict(binary_block_pairs=pairs,horizontal_compatible_pairs=hpairs,
                vertical_compatible_pairs=vpairs,compatible_three_cell_tuples=triples,
                state_membership_checked_at_all_three_sites=True)


def verify_tori():
    fields=accepted=period_checks=originals=relations=corruptions=random_fields=0
    exhaustive=[]
    for width,height in ((1,1),(1,2),(2,1)):
        valid_here=0
        for entries in product(BLOCKS,repeat=width*height):
            blocks=[list(entries[t*width:(t+1)*width]) for t in range(height)]
            okay=new_valid(blocks,lambda w:True)
            assert okay==(blocks==lift(project(blocks)))
            fields+=1
            if okay:accepted+=1;valid_here+=1
        assert valid_here==2**(width*height)
        exhaustive.append(dict(width=width,height=height,valid_fields=valid_here))
    predicates=(lambda w:True,lambda w:False,lambda w:bool(w[4]),
                lambda w:sum(w)%2==0,lambda w:w[1]==w[7],
                lambda w:w[4]==(w[3]^w[5]),lambda w:w[0]==w[8],lambda w:sum(w)>=4)
    shapes=((1,1),(1,2),(2,1),(1,3),(3,1),(2,2),(1,4),(4,1),(2,3),(3,2),(3,3))
    for width,height in shapes:
        for entries in product((0,1),repeat=width*height):
            grid=[list(entries[t*width:(t+1)*width]) for t in range(height)]
            blocks=lift(grid)
            assert project(blocks)==grid and lift(project(blocks))==blocks
            assert previous.periods(grid)==previous.periods(blocks)
            period_checks+=width*height;originals+=1
            for predicate in predicates:
                assert old_valid(grid,predicate)==new_valid(blocks,predicate);relations+=1
            # Every single-component defect destroys exact overlap reconstruction.
            for slot in range(9):
                bad=[row[:] for row in blocks];cell=list(bad[0][0]);cell[slot]^=1;bad[0][0]=tuple(cell)
                assert not new_valid(bad,lambda w:True);corruptions+=1
    rng=random.Random(739211)
    for width,height in ((2,2),(2,3),(3,2),(3,3)):
        for _ in range(250):
            blocks=[[rng.choice(BLOCKS) for _ in range(width)] for _ in range(height)]
            assert new_valid(blocks,lambda w:True)==(blocks==lift(project(blocks)))
            random_fields+=1
    return dict(exhaustive_arbitrary_block_fields=fields,exhaustive_valid_block_fields=accepted,
                exhaustive_shapes=exhaustive,binary_original_fields=originals,
                translation_residue_checks=period_checks,selected_relation_checks=relations,
                rejected_single_component_corruptions=corruptions,random_arbitrary_block_fields=random_fields,
                degenerate_dimensions_one_and_two_included=True)


def safe_thresholds(history,word):
    e=min(head for _,head,_ in history);f=max(head for _,head,_ in history)
    a=max(2,1-e);b=max(2,f-len(word)+2)
    return a,b,a+len(word)+b+1,max(3,len(history)+1)


def build_safe_torus(machine,word,history,width,height):
    a,b,wmin,hmin=safe_thresholds(history,word)
    assert width>=wmin and height>=hmin
    grid=[]
    for t in range(height):
        row=[]
        for x in range(width):
            if x==0 or t==0:
                row.append(tableau.tile(int(x==0),int(t==0)));continue
            tape,head,state=history[min(t-1,len(history)-1)]
            pos=x-a-1;payload=(tape.get(pos,machine.blank),state if pos==head else None)
            phase=None if t!=1 else 'L' if pos<0 else pos if pos<len(word) else 'R'
            row.append(tableau.tile(0,0,payload,phase))
        grid.append(row)
    return grid


def fixed_marker(machine):
    V=tableau.tile(1,0);H=tableau.tile(0,1);X=tableau.tile(1,1)
    Q=tableau.tile(0,0,(machine.blank,None))
    L=tableau.tile(0,0,(machine.blank,None),'L');R=tableau.tile(0,0,(machine.blank,None),'R')
    return (Q,V,Q,H,X,H,R,V,L)


def verify_marked():
    padded=repeated=cyclic=marker_occurrences=period_checks=bad_markers=0;records=[]
    for machine,word in previous.sample_machines():
        history=tableau.simulate(machine,word);assert history is not None
        a,b,wmin,hmin=safe_thresholds(history,word)
        predicate=previous.tableau_predicate(machine,word);marker=fixed_marker(machine)
        assert predicate(marker)
        records.append(dict(input=list(word),steps=len(history)-1,left_margin=a,right_margin=b,
                            width=wmin,height=hmin,marker_is_fixed=True))
        for width in range(wmin,wmin+5):
            for height in range(hmin,hmin+5):
                grid=build_safe_torus(machine,word,history,width,height)
                assert tableau.torus_valid(grid,machine,word)
                for t in range(1,height):
                    assert grid[t][1][2]==grid[t][-1][2]==(machine.blank,None)
                blocks=lift(grid)
                assert new_valid(blocks,predicate) and project(blocks)==grid
                assert blocks[0][0]==marker
                assert previous.periods(grid)==previous.periods(blocks);period_checks+=width*height
                assert sum(block==marker for row in blocks for block in row)==1
                marker_occurrences+=1;padded+=1
                repeated_blocks=[row*2 for row in blocks]*3
                assert new_valid(repeated_blocks,predicate)
                assert sum(block==marker for row in repeated_blocks for block in row)==6
                repeated+=1
                bad=[row[:] for row in blocks];cell=list(marker);cell[0]=marker[3];bad[0][0]=tuple(cell)
                assert not new_valid(bad,predicate);bad_markers+=1
        for hh in range(max(wmin-1,hmin),max(wmin-1,hmin)+5):
            grid=build_safe_torus(machine,word,history,hh+1,hh);blocks=lift(grid)
            length=hh*(hh+1);packed=[None]*length
            for t in range(hh):
                for x in range(hh+1):
                    i=(-hh*x-(hh+1)*t)%length
                    assert packed[i] is None;packed[i]=blocks[t][x]
            assert packed[0]==marker
            for i in range(length):
                assert three_valid(packed[i],packed[(i-hh)%length],packed[(i-hh-1)%length],predicate)
            cyclic+=1
    # No accidental conversion of a headless unframed configuration into a marked one.
    machine=previous.sample_machines()[1][0];word=(1,)
    unframed=[[tableau.tile(0,0,(0,None)) for _ in range(4)] for _ in range(3)]
    blocks=lift(unframed)
    assert new_valid(blocks,previous.tableau_predicate(machine,word))
    assert all(block!=fixed_marker(machine) for row in blocks for block in row)
    return dict(halting_examples=records,padded_tori=padded,rectangular_repetitions=repeated,
                fixed_marker_occurrences=marker_occurrences,translation_residue_checks=period_checks,
                rejected_marker_block_corruptions=bad_markers,consecutive_cyclic_presentations=cyclic,
                zero_step_halt_height_three_tested=True,boundary_adjacent_columns_always_blank_headless=True,
                unmarked_vacuity_stays_unmarked=True,
                marker='Q,V,Q / H,X,H / blank-R,V,blank-L; Q is blank headless with no phase')


def verify():
    return dict(status='PASS_THREE_CELL_PERIOD_LIFT',local=verify_local(),small_tori=verify_tori(),
                marked_tableaux=verify_marked(),proof='../1980/EXPLORATION_THREE_CELL_PERIOD_LIFT.md',
                arithmetic_operation_count=None,fixed_raw_input_universal_improvement=False,
                scope='Exact-period three-cell lift of every finite3x3 relation; fixed marked-TM block with independently larger blank margins; no arithmetic compiler')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['small_tori']['exhaustive_arbitrary_block_fields'],'arbitrary block fields;',
          result['marked_tableaux']['padded_tori'],'marked padded tori')
