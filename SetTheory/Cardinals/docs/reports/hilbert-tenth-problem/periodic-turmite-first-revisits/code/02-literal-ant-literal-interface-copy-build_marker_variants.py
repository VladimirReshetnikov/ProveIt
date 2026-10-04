#!/usr/bin/env python3
"""Joint physical marker-column histories with exclusive continuation branches."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,importlib.util,json,pathlib
P=pathlib.Path(__file__).resolve().parent;ROOT=P.parent
sp=importlib.util.spec_from_file_location('own_family',P/'build_normalized_copy_family.py');M=importlib.util.module_from_spec(sp);sp.loader.exec_module(M);R=M.R
SOURCE={'NOT':ROOT/'not/normalized_not.json','COPY':P/'normalized_copy.json'}
J={k:json.loads(p.read_text())for k,p in SOURCE.items()}
def pos(p,dy):return[p[0],p[1]+dy,*p[2:]]
def make(name):
 board={};owners={};blocked=set();placements=[];routes=[];aliases=[]
 def add_pl(pl):
  cells=R.transformed(M.CAT[pl['gadget']]['cell_map'],pl['offset'],pl['clockwise_quarter_turns']);ov=set(cells)&set(board)
  if ov:
   assert pl['gadget']=='box'and ov==set(cells)and len(ov)==43 and all(cells[p]==board[p]for p in ov)
   aliases.append({'new_resource':pl['label'],'existing_resources':sorted({owners[p]for p in ov}),'cell_count':43,'offset':pl['offset']})
  for p,c in cells.items():
   if p not in board:board[p]=c;owners[p]=pl['label']
  xs=[p[0]for p in cells];ys=[p[1]for p in cells];blocked.update((x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1));placements.append(pl)
 def add_rt(rt):
  cells={(x,y):c for x,y,c in rt['cells']};assert not(set(cells)&set(board));assert not(set(cells)&blocked)
  board.update(cells);owners.update({p:rt['label']for p in cells});routes.append(rt)
 if name=='right_stop':components=[('NOT',0,{'after_write'}),('COPY',200,{'enter'})];join=('union','TURN_MERGE',[551,308],3)
 else:components=[('COPY',200,{'written_merge'}),('NOT',400,{'enter'})];join=('union','START_MERGE',[21,472],1)
 for source,dy,excluded in components:
  for pl in J[source]['placements']:
   add_pl({'gadget':pl['gadget'],'label':source+'.'+pl['label'],'offset':pos(pl['offset'],dy),'clockwise_quarter_turns':pl['clockwise_quarter_turns']})
 for source,dy,excluded in components:
  for rt in J[source]['routes']:
   if rt['label']in excluded:continue
   add_rt({'label':source+'.'+rt['label'],'start':pos(rt['start'],dy),'terminal':pos(rt['terminal'],dy),'coarse_corridor_anchors':[pos(p,dy)for p in rt['coarse_corridor_anchors']],'states':[pos(p,dy)for p in rt['states']],'cells':[pos(p,dy)for p in rt['cells']]})
 gadget,label,off,k=join;add_pl({'gadget':gadget,'label':label,'offset':off,'clockwise_quarter_turns':k})
 if name=='right_stop':
  specs=[('early_turn',(107,249,0),(554,300,2),[(107,249),(107,220),(554,220),(554,300)]),('later_return',(600,305,3),(554,308,0),[(600,305),(580,305),(580,330),(554,330),(554,308)]),('merged_copy_entry',(550,305,3),(190,305,3),[(550,305),(190,305)])]
  ports={'forward_entry':(0,75,1),'forward_continue_exit':(600,75,1),'return_entry':(600,305,3),'return_exit':(0,305,3),'input_write_entry':(102,50,2),'input_write_exit':(107,49,0),'output_read_entry':(103,459,0),'output_zero_exit':(99,456,3),'output_one_exit':(109,456,1)};iy=50;oy=450
 else:
  specs=[('early_start',(140,388,2),(18,472,2),[(140,388),(140,410),(44,410),(44,460),(18,460),(18,472)]),('later_header_entry',(0,475,1),(18,480,0),[(0,475),(8,475),(8,500),(18,500),(18,480)]),('merged_not_entry',(22,475,1),(50,475,1),[(22,475),(50,475)])]
  ports={'return_entry':(600,305,3),'return_continue_exit':(0,305,3),'header_entry':(0,475,1),'header_exit':(600,475,1),'input_write_entry':(102,250,2),'input_write_exit':(107,249,0),'output_read_entry':(103,659,0),'output_zero_exit':(99,656,3),'output_one_exit':(109,656,1)};iy=250;oy=650
 for label,start,end,anchors in specs:
  states,cells=R.route(start,end,anchors,blocked,board);add_rt({'label':label,'start':start,'terminal':end,'coarse_corridor_anchors':anchors,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 cases=[]
 for kind in['INIT0','INIT1','WRITE0']:
  for read in[False,True]:
   b=board.copy();cnt=collections.Counter();traces=[];effective=int(kind!='INIT0');result=1-effective;phaseports=[]
   if kind=='INIT1':
    for p in[(104,iy+4),(105,iy+4)]:b[p]=0
   if kind=='WRITE0':phaseports.append(('input_write_entry','input_write_exit'))
   if name=='right_stop':phaseports += [('forward_entry','return_exit')]if effective==0 else[('forward_entry','forward_continue_exit'),('return_entry','return_exit')]
   else:phaseports += [('return_entry','header_exit')]if effective==1 else[('return_entry','return_continue_exit'),('header_entry','header_exit')]
   if read:phaseports.append(('output_read_entry','output_one_exit'if result else'output_zero_exit'))
   for a,z in phaseports:
    tr,c=R.run(b,ports[a],ports[z]);traces.append(tr);cnt.update(c)
    if z in['return_exit','header_exit']:assert b[104,oy+4]==b[105,oy+4]==1-result
   assert max(cnt.values())<=2
   cases.append({'input_kind':kind,'effective_input':effective,'logical_result':result,'later_output_read':read,'phase_ports':phaseports,'phase_steps':list(map(len,traces)),'phase_traces':traces,'max_aggregate_visits':max(cnt.values()),'twice_visited_cells':[list(p)for p in sorted(cnt)if cnt[p]==2],'final_changed_cells_basis':'common_INIT0_board','final_changed_cells':[[x,y,c]for(x,y),c in sorted(b.items())if board[x,y]!=c]})
 assert all(0<=x<=600 for x,y in board)
 out={'name':name,'status':'PASS_FINITE_JOINT_MARKER_COLUMN_ONLY','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'source_pins':{k:hashlib.sha256(p.read_bytes()).hexdigest()for k,p in SOURCE.items()},'width':600,'input_box_offset':[100,iy],'intermediate_box_offset':[100,iy+200],'output_box_offset':[100,oy],'placements':placements,'routes':routes,'aliases':aliases,'board':[[x,y,c]for(x,y),c in sorted(board.items())],'ownership':[[x,y,owners[x,y]]for x,y in sorted(board)],'cell_count':len(board),'ports':ports,'cases':cases,'limitations':['The two continuation branches are exclusive','Later external W entry is forbidden after an immediate right-stop branch','Later normal header E entry is forbidden after an immediate left-start branch','Separate continuation phases require the external row network','Only this joint finite map is certified, not independent normal-entry substitution']}
 (P/f'marker_{name}.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'name':name,'cells':len(board),'routes':len(routes),'phases':[c['phase_steps']for c in cases]}),flush=True)

def main():
 for name in['right_stop','left_start']:make(name)
if __name__=='__main__':main()
