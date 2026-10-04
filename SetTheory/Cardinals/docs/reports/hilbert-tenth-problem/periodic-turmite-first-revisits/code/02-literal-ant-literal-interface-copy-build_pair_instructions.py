#!/usr/bin/env python3
"""Finite delayed two-slot DUP/MOVE_RIGHT/MOVE_LEFT instruction maps."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,importlib.util,itertools,json,pathlib
P=pathlib.Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('own_family',P/'build_normalized_copy_family.py');M=importlib.util.module_from_spec(sp);sp.loader.exec_module(M);R=M.R

def build(name,selected,write_indices):
 s=600*selected;X=lambda x:x+s;xx=[100,700];outs=[xx[i]for i in write_indices];board={};owners={};blocked=set();placements=[]
 specs=[('box',f'input_{i}',(x,50),0)for i,x in enumerate(xx)]+[('box',f'output_{i}',(x,450),0)for i,x in enumerate(xx)]+[('cruceB','forward_zero_cross',(X(34),75),0),('cruceA','forward_read_cross',(X(94),75),0),('cruceB','forward_one_cross',(X(220),81),0),('cruceA','read_cross',(X(190),305),2),('cruceB','write_cross',(X(140),381),0),('union','merge',(X(41),308),3)]
 for gadget,label,off,k in specs:
  cells=R.transformed(M.CAT[gadget]['cell_map'],off,k);assert not(set(cells)&set(board));board.update(cells);owners.update({p:label for p in cells});xs=[p[0]for p in cells];ys=[p[1]for p in cells]
  blocked.update((x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1));placements.append({'gadget':gadget,'label':label,'offset':off,'clockwise_quarter_turns':k})
 ss=[
 ('forward_enter',(0,75,1),(X(34),75,1),[(0,75),(X(34),75)]),
 ('forward_zero_to_read',(X(40),81,1),(X(94),75,1),[(X(40),81),(X(70),81),(X(70),75),(X(94),75)]),
 ('forward_read_to_one',(X(100),81,1),(X(220),81,1),[(X(100),81),(X(220),81)]),
 ('forward_leave',(X(226),87,1),(1200,75,1),[(X(226),87),(X(270),87),(X(270),75),(1200,75)]),
 ('enter',(1200,305,3),(X(190),305,3),[(1200,305),(X(190),305)]),
 ('to_read_cross',(X(184),299,3),(X(94),81,1),[(X(184),299),(X(90),299),(X(90),81),(X(94),81)]),
 ('read_input',(X(100),75,1),(X(103),59,0),[(X(100),75),(X(103),75),(X(103),59)]),
 ('one_to_forward_cross',(X(109),56,1),(X(225),82,3),[(X(109),56),(X(250),56),(X(250),82),(X(225),82)]),
 ('one_to_read_cross',(X(220),88,2),(X(190),299,3),[(X(220),88),(X(220),299),(X(190),299)]),
 ('between_crossings',(X(184),305,3),(X(140),381,1),[(X(184),305),(X(130),305),(X(130),381),(X(140),381)]),
 ('write_first_output',(X(146),387,1),(outs[0]+2,450,2),[(X(146),387),(X(160),387),(X(160),420),(outs[0]+2,420),(outs[0]+2,450)]),
 ]
 for a,b in zip(outs,outs[1:]):ss.append((f'write_chain_{a}_{b}',(a+7,449,0),(b+2,450,2),[(a+7,449),(a+7,430),(b+2,430),(b+2,450)]))
 far=max(X(190),outs[-1]+90)
 ss +=[
 ('after_write',(outs[-1]+7,449,0),(X(145),382,3),[(outs[-1]+7,449),(outs[-1]+7,430),(far,430),(far,382),(X(145),382)]),
 ('written_merge',(X(140),388,2),(X(44),308,0),[(X(140),388),(X(140),410),(X(44),410),(X(44),308)]),
 ('zero_to_forward_cross',(X(99),56,3),(X(39),76,3),[(X(99),56),(X(50),56),(X(50),76),(X(39),76)]),
 ('zero_merge',(X(34),82,2),(X(44),300,2),[(X(34),82),(X(34),280),(X(44),280),(X(44),300)]),
 ('leave',(X(40),305,3),(0,305,3),[(X(40),305),(0,305)]),
 ]
 routes=[]
 for label,start,end,anchors in ss:
  states,cells=R.route(start,end,anchors,blocked,board);assert not(set(cells)&(set(board)|blocked)),label
  board.update(cells);owners.update({p:label for p in cells});routes.append({'label':label,'start':start,'terminal':end,'coarse_corridor_anchors':anchors,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 ports={'forward_entry':(0,75,1),'forward_exit':(1200,75,1),'entry':(1200,305,3),'exit':(0,305,3)}
 for i,x in enumerate(xx):ports.update({f'input_{i}_write_entry':(x+2,50,2),f'input_{i}_write_exit':(x+7,49,0),f'output_{i}_read_entry':(x+3,459,0),f'output_{i}_zero_exit':(x-1,456,3),f'output_{i}_one_exit':(x+9,456,1)})
 cases=[];histories=[]
 for kinds in itertools.product(['INIT0','INIT1','WRITE0'],repeat=2):
  written=[i for i,k in enumerate(kinds)if k=='WRITE0'];writeorders=list(itertools.permutations(written))
  for wo in writeorders:
   b=board.copy();cnt=collections.Counter();traces=[];phases=[];effective=[int(k!='INIT0')for k in kinds];out=[effective[selected]if i in write_indices else 0 for i in range(2)]
   for i,k in enumerate(kinds):
    if k=='INIT1':
     for p in[(xx[i]+4,54),(xx[i]+5,54)]:b[p]=0
   phases=[(f'input_{i}_write_entry',f'input_{i}_write_exit')for i in wo]+[('forward_entry','forward_exit'),('entry','exit')]
   ignored_before=None
   for a,z in phases:
    before={p:b[p]for p in board if owners[p].startswith('input_')}
    if a=='entry':ignored_before={p:b[p]for p in board if owners[p]==f'input_{1-selected}'}
    tr,c=R.run(b,ports[a],ports[z]);traces.append(tr);cnt.update(c)
    if a=='forward_entry':assert before=={p:b[p]for p in before}
   assert ignored_before=={p:b[p]for p in ignored_before}
   assert all(b[x+4,454]==b[x+5,454]==1-out[i]for i,x in enumerate(xx));before_reads=b.copy();before_counts=cnt.copy();otr=[]
   for i in range(2):tr,c=R.run(b,ports[f'output_{i}_read_entry'],ports[f'output_{i}_{"one"if out[i]else"zero"}_exit']);otr.append(tr);cnt.update(c)
   assert max(cnt.values())<=2
   ci=len(cases);cases.append({'input_kinds':kinds,'prior_write_order':wo,'effective_inputs':effective,'logical_outputs':out,'pre_read_phase_ports':phases,'pre_read_phase_steps':list(map(len,traces)),'pre_read_phase_traces':traces,'output_read_phase_traces':otr,'output_read_phase_steps':list(map(len,otr)),'max_aggregate_visits_after_all_reads':max(cnt.values()),'twice_visited_cells_after_all_reads':[list(p)for p in sorted(cnt)if cnt[p]==2],'final_changed_cells_basis':'common_INIT0_board','final_changed_cells_after_all_reads':[[x,y,c]for(x,y),c in sorted(b.items())if board[x,y]!=c]})
   for k in range(3):
    for order in itertools.permutations(range(2),k):
     bb=before_reads.copy();cc=before_counts.copy();tt=traces.copy()
     for i in order:tr,c=R.run(bb,ports[f'output_{i}_read_entry'],ports[f'output_{i}_{"one"if out[i]else"zero"}_exit']);assert tr==otr[i];cc.update(c);tt.append(tr)
     assert max(cc.values())<=2;histories.append({'input_case_index':ci,'output_read_order':order,'phase_steps':list(map(len,tt)),'trace_sha256':hashlib.sha256(json.dumps(tt,separators=(',',':')).encode()).hexdigest(),'max_aggregate_visits':max(cc.values())})
 assert all(0<=x<=1200 for x,y in board)
 delayed=json.loads((P/'delayed_copy.json').read_text());db={(x,y)for x,y,c in delayed['board']}
 assert not set(board)&{(x+1200,y)for x,y in db};assert not db&{(x+600,y)for x,y in board}
 return{'name':name,'status':'PASS_FINITE_DELAYED_PAIR_INSTRUCTION_ONLY','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'selected_input_index':selected,'ignored_input_index':1-selected,'written_output_indices':write_indices,'zero_output_indices':[i for i in range(2)if i not in write_indices],'input_box_offsets':[[x,50]for x in xx],'output_box_offsets':[[x,450]for x in xx],'placements':placements,'routes':routes,'board':[[x,y,c]for(x,y),c in sorted(board.items())],'ownership':[[x,y,owners[x,y]]for x,y in sorted(board)],'cell_count':len(board),'ports':ports,'cases':cases,'all_optional_read_histories':histories,'column_pitch':600,'width':1200,'parity_invariant':0,'neighbor_delayed_copy_disjoint_both_sides':True,'limitations':['All prior input WRITEs precede E pass','E activation must precede W activation; physical turnaround is external','Ignored input has only INIT0/INIT1/WRITE history and is never READ','Zero output boxes exist and are never written','Finite pair instruction map alone is not a universal compiler']}

def main():
 for name,selected,written in[('dup',0,[0,1]),('move_right',0,[1]),('move_left',1,[0])]:
  o=build(name,selected,written);(P/f'pair_{name}.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps({'name':name,'cells':o['cell_count'],'input_cases':len(o['cases']),'optional_read_histories':len(o['all_optional_read_histories']),'phase_steps':[c['pre_read_phase_steps']for c in o['cases']]}),flush=True)
if __name__=='__main__':main()
