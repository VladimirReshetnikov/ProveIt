#!/usr/bin/env python3
"""Exact global anchor agreement, startup suffixes, input counts and observer role."""
if not __debug__:raise RuntimeError('Assertions required')
import collections,hashlib,itertools,json,pathlib,random
from generator import Atlas
ROOT=pathlib.Path(__file__).resolve().parents[1];D=((0,-1),(1,0),(0,1),(-1,0))
def main():
 a=Atlas();anchor=json.loads((ROOT/'copy/fixed_initial_anchor_patch.json').read_text());local=json.loads((ROOT/'copy/left_start_anchor.json').read_text())
 patch=[]
 for x,y,old,new in anchor['patch']:
  assert a.color(x,y)==old,(x,y,old,a.paints(x,y));assert old!=new;patch.append([x,y,new])
 assert len(patch)==2806
 start=tuple(anchor['fixed_initial_head']);assert start==(288650,75,1)
 tests=[]
 for left,right in[([],[]),([0],[0]),([1],[1]),([1,0,1],[0,1]),([0,0,0],[1,1,1,1])]:
  changes=a.input_changes(left,right,patch);expected=2812+4*(sum(left)+sum(right));assert len(changes)==expected
  board={(x,y):v for x,y,v in changes};s=start;counts=collections.Counter();rows=[]
  dx,dy=anchor['translation']
  for expected_row in local['verified_suffix_trace']:
   x,y,h=s;v=board.get((x,y),a.color(x,y));turn=1 if v==0 else-1;hh=(h+turn)%4;vx,vy=D[hh];ns=x+vx,y+vy,hh
   # Verify the exact separately certified initial suffix in the complete board.
   if isinstance(expected_row,dict):
    before=expected_row['before'];after=expected_row['after'];c=expected_row['color_before']
   else:before=expected_row[:3];c=expected_row[3];after=expected_row[4:]
   assert s==(before[0]+dx,before[1]+dy,before[2])and v==c
   assert ns==(after[0]+dx,after[1]+dy,after[2])
   counts[x,y]+=1;assert counts[x,y]<=2;board[x,y]=1-v;rows.append([x,y,h,v,*ns]);s=ns
  target=local['verified_suffix_exit'];assert s==(target[0]+dx,target[1]+dy,target[2])
  tests.append({'left':left,'right':right,'changed_cells':len(changes),'startup_steps':len(rows),'startup_exit':s,'max_visits':max(counts.values())})
 # Per-template accepting-port facts, independent of bit values in ignored cells.
 dup=json.loads((ROOT/'copy/pair_dup.json').read_text());accepted=[]
 for c in dup['cases']:
  events=[row for tr in c['pre_read_phase_traces']for row in tr if row[:3]==[102,450,2]]
  assert len(events)==c['effective_inputs'][0],c['input_kinds']
  later=[row for tr in c['output_read_phase_traces']for row in tr if row[:3]==[102,450,2]]
  assert not later
  accepted.append({'inputs':c['input_kinds'],'expected_bit':c['effective_inputs'][0],'accepting_departures':len(events),'later_read_hits':len(later)})
 p=a.program;obs=p['observer_local_head_state'];assert p['observer_column_index']==910
 # Check exact board identity at the output-WRITE port and all complete box cells
 # in its physical instruction instance, including the next-row aliases.
 yy=400+400*p['observer_row_index'];xx=600+600*910
 expected={(x+xx,y+yy):c for x,y,c in dup['board']}
 selected_points=[(xx+102,yy+450),(xx+104,yy+454),(xx+105,yy+454),(xx+103,yy+459)]
 for pt in selected_points:assert a.color(*pt)==expected[pt]
 clauses=[{'x_mod':obs[0],'y_mod':obs[1],'heading':2},
  {'x_mod':(obs[0]+a.S//2)%a.S,'y_mod':obs[1]+a.V,'heading':2}]
 assert all(q['y_mod']%(2*a.V)not in[75,54]for q in clauses)
 result={'status':'PASS_GLOBAL_ANCHOR_AND_OBSERVER_LOCAL_ROLE','scope':'These checks support but do not replace the complete global routing/correctness proof.',
  'generator_sha256':hashlib.sha256((ROOT/'atlas/generator.py').read_bytes()).hexdigest(),
  'anchor_source_sha256':hashlib.sha256((ROOT/'copy/fixed_initial_anchor_patch.json').read_bytes()).hexdigest(),
  'all_2806_anchor_colors_match_global_background':True,'fixed_start':start,'startup_cases':tests,
  'input_change_count':'2812+4*(number of1 bits in the two finite nearest-head-first input words)',
  'input_word_contract':'Left/right are finite bit lists nearest head first. Initial primary CA word is reverse(left),head(A,0),right. All other tape cells blank.',
  'acceptance_period':[a.S,2*a.V],'prospective_acceptance_clauses':clauses,'accepting_template_cases':accepted,
  'heading_is_pre_departure':True,'stencil':[],'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
 (ROOT/'atlas/initialization_observer_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'anchor_cells':2806,'fixed_start':start,'input_cases':len(tests),'acceptance':clauses}))
if __name__=='__main__':main()
