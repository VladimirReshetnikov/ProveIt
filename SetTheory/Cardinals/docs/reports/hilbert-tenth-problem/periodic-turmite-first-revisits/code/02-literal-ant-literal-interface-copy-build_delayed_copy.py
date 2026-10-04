#!/usr/bin/env python3
"""Two-activation finite delayed COPY with a forward priming pass."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,importlib.util,json,pathlib
P=pathlib.Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('own_family',P/'build_normalized_copy_family.py');M=importlib.util.module_from_spec(sp);sp.loader.exec_module(M);R=M.R

def main():
 board={};owners={};blocked=set();placements=[]
 specs=[('box','input',(100,50),0),('box','output',(100,450),0),('cruceB','forward_zero_cross',(34,75),0),('cruceA','forward_read_cross',(94,75),0),('cruceB','forward_one_cross',(220,81),0),('cruceA','read_cross',(190,305),2),('cruceB','write_cross',(140,381),0),('union','merge',(41,308),3)]
 for gadget,label,off,k in specs:
  cells=R.transformed(M.CAT[gadget]['cell_map'],off,k);assert not(set(cells)&set(board));board.update(cells);owners.update({p:label for p in cells});xs=[p[0]for p in cells];ys=[p[1]for p in cells]
  blocked.update((x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1));placements.append({'gadget':gadget,'label':label,'offset':off,'clockwise_quarter_turns':k})
 ss=[
 ('forward_enter',(0,75,1),(34,75,1),[(0,75),(34,75)]),
 ('forward_zero_to_read',(40,81,1),(94,75,1),[(40,81),(70,81),(70,75),(94,75)]),
 ('forward_read_to_one',(100,81,1),(220,81,1),[(100,81),(220,81)]),
 ('forward_leave',(226,87,1),(600,75,1),[(226,87),(270,87),(270,75),(600,75)]),
 ('enter',(600,305,3),(190,305,3),[(600,305),(190,305)]),
 ('to_read_cross',(184,299,3),(94,81,1),[(184,299),(90,299),(90,81),(94,81)]),
 ('read_input',(100,75,1),(103,59,0),[(100,75),(103,75),(103,59)]),
 ('one_to_forward_cross',(109,56,1),(225,82,3),[(109,56),(250,56),(250,82),(225,82)]),
 ('one_to_read_cross',(220,88,2),(190,299,3),[(220,88),(220,299),(190,299)]),
 ('between_crossings',(184,305,3),(140,381,1),[(184,305),(130,305),(130,381),(140,381)]),
 ('write_output',(146,387,1),(102,450,2),[(146,387),(160,387),(160,420),(102,420),(102,450)]),
 ('after_write',(107,449,0),(145,382,3),[(107,449),(107,430),(190,430),(190,382),(145,382)]),
 ('written_merge',(140,388,2),(44,308,0),[(140,388),(140,410),(44,410),(44,308)]),
 ('zero_to_forward_cross',(99,56,3),(39,76,3),[(99,56),(50,56),(50,76),(39,76)]),
 ('zero_merge',(34,82,2),(44,300,2),[(34,82),(34,280),(44,280),(44,300)]),
 ('leave',(40,305,3),(0,305,3),[(40,305),(0,305)]),
 ]
 routes=[]
 for label,start,end,anchors in ss:
  states,cells=R.route(start,end,anchors,blocked,board);assert not(set(cells)&(set(board)|blocked)),label
  board.update(cells);owners.update({p:label for p in cells});routes.append({'label':label,'start':start,'terminal':end,'coarse_corridor_anchors':anchors,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 ports={'forward_entry':(0,75,1),'forward_exit':(600,75,1),'entry':(600,305,3),'exit':(0,305,3),'input_write_entry':(102,50,2),'input_write_exit':(107,49,0),'output_read_entry':(103,459,0),'output_zero_exit':(99,456,3),'output_one_exit':(109,456,1)}
 assert all(M.inv(s)==0 for s in ports.values())
 # A prior WRITE can happen before or after the unrelated forward pass; both are verified.
 histories=[]
 for initial,timing in[(0,None),(1,None),(0,'before_forward'),(0,'after_forward')]:
  for read in[False,True]:
   b=board.copy();cnt=collections.Counter();traces=[];phases=[];out=1 if timing else initial
   if initial:
    for p in[(104,54),(105,54)]:b[p]=0
   phases+= [('input_write_entry','input_write_exit')]if timing=='before_forward'else[]
   phases+=[('forward_entry','forward_exit')]
   phases+= [('input_write_entry','input_write_exit')]if timing=='after_forward'else[]
   phases+=[('entry','exit')]
   if read:phases+=[('output_read_entry','output_one_exit'if out else'output_zero_exit')]
   checkpoints=[]
   for a,z in phases:
    before={p:b[p]for p in board if owners[p]=='input'}
    tr,c=R.run(b,ports[a],ports[z]);traces.append(tr);cnt.update(c)
    if a=='forward_entry':assert before=={p:b[p]for p in before},'forward touched input box'
    if a=='entry':assert b[104,454]==b[105,454]==1-out
    checkpoints.append({'phase':a,'max_aggregate_departures':max(cnt.values()),'input_state_cell_colors':[b[104,54],b[105,54]],'output_state_cell_colors':[b[104,454],b[105,454]]})
   assert max(cnt.values())<=2
   history={'initial_input':initial,'prior_write_timing':timing,'later_output_read':read,'logical_result':out,'phase_ports':phases,'phase_steps':list(map(len,traces)),'phase_traces':traces,'phase_checkpoints':checkpoints,'max_aggregate_visits':max(cnt.values()),'twice_visited_cells':[list(p)for p in sorted(cnt)if cnt[p]==2],'final_changed_cells_basis':'common_INIT0_board','final_changed_cells':[[x,y,c]for(x,y),c in sorted(b.items())if board[x,y]!=c]}
   histories.append(history)
 # Separate same-row neighbors meet at exact direction-specific seam states without overlap.
 assert not set(board)&{(x+600,y)for x,y in board}
 out={'name':'delayed_copy','status':'PASS_FINITE_TWO_ACTIVATION_DELAYED_COPY_ONLY','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'placements':placements,'routes':routes,'board':[[x,y,c]for(x,y),c in sorted(board.items())],'ownership':[[x,y,owners[x,y]]for x,y in sorted(board)],'cell_count':len(board),'ports':ports,'cases':histories,'column_pitch':600,'input_box_offset':[100,50],'output_box_offset':[100,450],'parity_invariant':0,'neighbor_translation_600_disjoint':True,'limitations':['Forward E activation must precede W activation','Input is consumed only by W activation','Between phases the external network must physically connect exact ports','Finite delayed-copy tile alone does not prove complete instruction-row atlas']}
 (P/'delayed_copy.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'cells':len(board),'routes':len(routes),'histories':len(histories),'phases':[h['phase_steps']for h in histories]}))
if __name__=='__main__':main()
