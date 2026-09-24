#!/usr/bin/env python3
"""Period-preserving vertical-triple lift of a radius-one local relation.

This is a finite-alphabet interface theorem, not an arithmetic SLP count.
"""
from itertools import product
from pathlib import Path
import json
import sys

import explore_marked_periodic_tm_padding as tableau

OUT=Path(__file__).with_suffix('.json')
TRIPLES=tuple(product((0,1),repeat=3))


def lift(grid):
    height,width=len(grid),len(grid[0])
    return [[tuple(grid[(t+dt)%height][x] for dt in (-1,0,1))
             for x in range(width)] for t in range(height)]


def project(grid):
    return [[cell[1] for cell in row] for row in grid]


def window(grid,x,t):
    height,width=len(grid),len(grid[0])
    return tuple(grid[(t+dt)%height][(x+dx)%width]
                 for dt in (-1,0,1) for dx in (-1,0,1))


def column_window(left,center,right):
    return tuple(column[row] for row in range(3) for column in (left,center,right))


def four_valid(left,center,right,nxt,predicate):
    return (nxt[0]==center[1] and nxt[1]==center[2]
            and predicate(column_window(left,center,right)))


def old_valid(grid,predicate):
    return all(predicate(window(grid,x,t))
               for t in range(len(grid)) for x in range(len(grid[0])))


def new_valid(grid,predicate):
    height,width=len(grid),len(grid[0])
    return all(four_valid(grid[t][(x-1)%width],grid[t][x],grid[t][(x+1)%width],
                          grid[(t+1)%height][x],predicate)
               for t in range(height) for x in range(width))


def periods(grid):
    height,width=len(grid),len(grid[0])
    return {(dx,dt) for dx in range(width) for dt in range(height)
            if all(grid[(t+dt)%height][(x+dx)%width]==grid[t][x]
                   for t in range(height) for x in range(width))}


def verify_local_table():
    quads=overlap=0;windows=set()
    for left,center,right,nxt in product(TRIPLES,repeat=4):
        expected_overlap=nxt[:2]==center[1:]
        pattern=column_window(left,center,right)
        assert four_valid(left,center,right,nxt,lambda w:True)==expected_overlap
        assert not four_valid(left,center,right,nxt,lambda w:False)
        assert four_valid(left,center,right,nxt,lambda w:w==pattern)==expected_overlap
        assert not four_valid(left,center,right,nxt,lambda w:w!=pattern)
        if expected_overlap:overlap+=1;windows.add(pattern)
        quads+=1
    assert quads==4096 and overlap==1024 and len(windows)==512
    return dict(binary_four_cell_tuples=quads,overlap_compatible_tuples=overlap,
                distinct_original_windows=len(windows),membership_polarities_checked=2,
                observation='Each original window has exactly two compatible next triple states')


def verify_small_tori():
    shapes=((1,1),(1,2),(2,1),(1,3),(3,1),(2,2),(1,4),(4,1),(2,3),(3,2))
    fields=overlap_fields=period_checks=originals=relation_checks=0;shape_records=[]
    predicates=(lambda w:True,lambda w:False,lambda w:w[4]==1,
                lambda w:sum(w)%2==0,lambda w:w[1]==w[7],
                lambda w:w[4]==(w[3]^w[5]),lambda w:w[0]==w[8],
                lambda w:sum(w)>=4)
    for width,height in shapes:
        accepted_here=0
        for entries in product(TRIPLES,repeat=width*height):
            grid=[list(entries[t*width:(t+1)*width]) for t in range(height)]
            overlap_ok=new_valid(grid,lambda w:True)
            reconstructed=lift(project(grid))
            assert overlap_ok==(grid==reconstructed)
            fields+=1
            if not overlap_ok:continue
            overlap_fields+=1;accepted_here+=1
            assert periods(grid)==periods(project(grid));period_checks+=width*height
        assert accepted_here==2**(width*height)
        for entries in product((0,1),repeat=width*height):
            grid=[list(entries[t*width:(t+1)*width]) for t in range(height)]
            lifted=lift(grid)
            assert project(lifted)==grid and lift(project(lifted))==lifted
            assert periods(grid)==periods(lifted)
            for t in range(height):
                for x in range(width):
                    assert window(grid,x,t)==column_window(
                        lifted[t][(x-1)%width],lifted[t][x],lifted[t][(x+1)%width])
            for predicate in predicates:
                assert old_valid(grid,predicate)==new_valid(lifted,predicate)
                relation_checks+=1
            originals+=1
        shape_records.append(dict(width=width,height=height,valid_overlap_fields=accepted_here))
    return dict(exhausted_triple_fields=fields,overlap_valid_fields=overlap_fields,
                binary_original_fields=originals,translation_residue_checks=period_checks,
                selected_relation_torus_checks=relation_checks,shapes=shape_records,
                degenerate_dimensions_one_and_two_included=True)


def sample_machines():
    stationary=tableau.make_machine(('H',),{},start='H')
    sweep=tableau.make_machine(('q','H'),{('q',1):('q',1,1)})
    excursion=tableau.make_machine(('q','a','b','c','H'),{
        (q,a):(nextq,a,d)
        for q,nextq,d in (('q','a',-1),('a','b',-1),('b','c',1),('c','H',0))
        for a in (0,1)})
    rewrite=tableau.make_machine(('q','a','b','H'),{
        (q,a):(nextq,written,d)
        for q,nextq,written,d in (('q','a',1,1),('a','b',0,-1),('b','H',1,0))
        for a in (0,1)})
    return [(stationary,(0,)),(sweep,(1,1,1)),(excursion,(1,)),(rewrite,(0,1))]


def tableau_predicate(machine,word):
    def predicate(w):
        at=lambda dx,dt:w[(dt+1)*3+dx+1]
        return tableau.local_valid(w[4],at,machine,word)
    return predicate


def verify_marked_examples():
    V=tableau.tile(1,0);X=tableau.tile(1,1);marker=(V,X,V)
    padded=repeated=cyclic=marker_cells=period_checks=corruptions=0;thresholds=[]
    for machine,word in sample_machines():
        history=tableau.simulate(machine,word);assert history is not None
        a,b,wmin,hmin=tableau.thresholds(history,word)
        predicate=tableau_predicate(machine,word)
        thresholds.append(dict(input=list(word),steps=len(history)-1,width=wmin,height=hmin))
        for width in range(wmin,wmin+5):
            for height in range(hmin,hmin+5):
                grid=tableau.build_torus(machine,word,history,width,height)
                assert tableau.torus_valid(grid,machine,word)
                lifted=lift(grid);assert new_valid(lifted,predicate) and project(lifted)==grid
                assert periods(grid)==periods(lifted);period_checks+=width*height
                for t in range(height):
                    for x in range(width):
                        assert (grid[t][x]==X)==(lifted[t][x]==marker)
                        marker_cells+=grid[t][x]==X
                assert lifted[0][0]==marker
                padded+=1
                doubled=[row*2 for row in lifted]*3
                assert new_valid(doubled,predicate)
                assert project(doubled)==[row*2 for row in grid]*3;repeated+=1
                # An inconsistent triple is rejected by overlap alone.
                corrupt=[row[:] for row in lifted]
                old=corrupt[0][0];corrupt[0][0]=(X,old[1],old[2])
                assert not new_valid(corrupt,predicate);corruptions+=1
        for hh in range(max(wmin-1,hmin),max(wmin-1,hmin)+5):
            grid=tableau.build_torus(machine,word,history,hh+1,hh);lifted=lift(grid)
            length=hh*(hh+1);packed=[None]*length
            for t in range(hh):
                for x in range(hh+1):
                    index=(-hh*x-(hh+1)*t)%length
                    assert packed[index] is None;packed[index]=lifted[t][x]
            assert marker in packed
            for i in range(length):
                assert four_valid(packed[(i+hh)%length],packed[i],packed[(i-hh)%length],
                                  packed[(i-hh-1)%length],predicate)
            cyclic+=1
    # The original unmarked vacuity remains unmarked under the bijection.
    machine=sample_machines()[1][0];word=(1,)
    unframed=[[tableau.tile(0,0,(0,None)) for _ in range(4)] for _ in range(3)]
    lifted=lift(unframed)
    assert new_valid(lifted,tableau_predicate(machine,word))
    assert all(cell!=marker for row in lifted for cell in row)
    return dict(halting_examples=thresholds,padded_tori=padded,rectangular_repetitions=repeated,
                fixed_marker_occurrences=marker_cells,translation_residue_checks=period_checks,
                rejected_triple_corruptions=corruptions,consecutive_cyclic_presentations=cyclic,
                minimum_height_two_included=True,unmarked_vacuity_stays_unmarked=True,
                marker='(vertical boundary, intersection X, vertical boundary)')


def verify():
    return dict(status='PASS_FOUR_CELL_PERIOD_LIFT',local=verify_local_table(),
                small_tori=verify_small_tori(),marked_tableaux=verify_marked_examples(),
                proof='../1980/EXPLORATION_FOUR_CELL_PERIOD_LIFT.md',
                universal_certificate_improvement=False,arithmetic_operation_count=None,
                scope='Uniform four-cell finite relation exactly conjugate to the original3x3 relation; exact period lattices and fixed marked-tableau marker; no raw-input arithmetic compiler')


if __name__=='__main__':
    result=verify()
    if sys.argv[1:]==['--write']:
        OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    else:
        assert not sys.argv[1:]
        assert result==json.loads(OUT.read_text(encoding='utf-8'))
    print(result['status'],result['small_tori']['exhausted_triple_fields'],'triple fields;',
          result['marked_tableaux']['padded_tori'],'marked padded tori')
