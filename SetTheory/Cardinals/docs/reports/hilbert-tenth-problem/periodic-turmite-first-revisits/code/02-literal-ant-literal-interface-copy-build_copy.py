#!/usr/bin/env python3
"""Own literal COPY construction from source RL primitive maps; never source code execution."""
if not __debug__: raise RuntimeError('Run without -O')
import collections,hashlib,importlib.util,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
COMMON=HERE.parent/'common'
spec=importlib.util.spec_from_file_location('previous_own_router',COMMON/'geometry_kit.py')
router=importlib.util.module_from_spec(spec);spec.loader.exec_module(router)
D=router.D

def main():
 catalog=json.loads((COMMON/'primitive_maps.json').read_text())
 board={};blocked=set();owners={};placements=[]
 for name,label,offset,k in [('box','input',(100,50),0),('box','output',(100,250),0),('cruceA','read_cross',(190,105),2),('cruceB','write_cross',(140,181),0),('union','merge',(41,108),3)]:
  cells=router.transformed(catalog[name]['cell_map'],offset,k)
  assert not(set(cells)&set(board));board.update(cells);owners.update({p:label for p in cells})
  xs=[p[0] for p in cells];ys=[p[1] for p in cells]
  blocked.update((x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1))
  placements.append({'gadget':name,'label':label,'offset':offset,'clockwise_quarter_turns':k})
 specs=[
 ('enter',(300,105,3),(190,105,3),[(300,105),(190,105)]),
 ('read_input',(184,99,3),(103,59,0),[(184,99),(103,99),(103,59)]),
 ('one_cross',(109,56,1),(190,99,3),[(109,56),(220,56),(220,99),(190,99)]),
 ('between_crossings',(184,105,3),(140,181,1),[(184,105),(130,105),(130,181),(140,181)]),
 ('write_output',(146,187,1),(102,250,2),[(146,187),(160,187),(160,220),(102,220),(102,250)]),
 ('after_write',(107,249,0),(145,182,3),[(107,249),(107,230),(190,230),(190,182),(145,182)]),
 ('written_merge',(140,188,2),(44,108,0),[(140,188),(140,210),(44,210),(44,108)]),
 ('zero_merge',(99,56,3),(44,100,2),[(99,56),(44,56),(44,100)]),
 ('leave',(40,105,3),(0,105,3),[(40,105),(0,105)]),
 ]
 routes=[]
 for label,start,target,anchors in specs:
  states,cells=router.route(start,target,anchors,blocked,board)
  assert not(set(cells)&set(board)),('overlap',label)
  assert not(set(cells)&blocked),('core rectangle overlap',label)
  board.update(cells);owners.update({p:label for p in cells})
  routes.append({'label':label,'start':start,'terminal':target,'coarse_corridor_anchors':anchors,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 cases=[]
 for initial,written in [(0,False),(1,False),(0,True)]:
  b=board.copy();traces=[];counts=collections.Counter()
  if initial:
   for p in[(104,54),(105,54)]:assert b[p]==1;b[p]=0
  if written:
   r,c=router.run(b,(102,50,2),(107,49,0));traces.append(r);counts.update(c)
  r,c=router.run(b,(300,105,3),(0,105,3));traces.append(r);counts.update(c)
  output=1 if written else initial
  assert b[104,254]==b[105,254]==1-output
  terminal=(109,256,1)if output else(99,256,3)
  r,c=router.run(b,(103,259,0),terminal);traces.append(r);counts.update(c)
  assert max(counts.values())<=2
  events=[]
  entry_table={(190,105,3):('read_cross','FIRST'),(190,99,3):('read_cross','SECOND'),(140,181,1):('write_cross','FIRST'),(145,182,3):('write_cross','SECOND'),(44,100,2):('merge','RIGHT'),(44,108,0):('merge','LEFT'),(103,59,0):('input','READ'),(102,250,2):('output','WRITE')}
  macrotrace=traces[-2]
  for row in macrotrace:
   if tuple(row[:3]) in entry_table:events.append({'step':macrotrace.index(row),'component':entry_table[tuple(row[:3])][0],'operation':entry_table[tuple(row[:3])][1]})
  cases.append({'initial_input':initial,'prior_input_write':written,'logical_result':output,'phase_steps':list(map(len,traces)),'max_aggregate_visits':max(counts.values()),'twice_visited_cells':[list(p)for p in sorted(counts)if counts[p]==2],'phase_traces':traces,'macro_events':events,'final_changed_cells_basis':'common_INIT0_board','final_changed_cells':[[x,y,c]for(x,y),c in sorted(b.items())if board[x,y]!=c]})
 ports={'entry':[300,105,3],'exit':[0,105,3],'input_write_entry':[102,50,2],'input_write_exit':[107,49,0],'output_read_entry':[103,259,0],'output_zero_exit':[99,256,3],'output_one_exit':[109,256,1]}
 result={'status':'PASS_FINITE_COPY_MACRO_ONLY','scope':'One original-orientation input box above one original-orientation output box, with right-to-left control. Literal source primitives and own finite connecting routes. Not a periodic atlas or universal compiler.',
 'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'catalog_sha256':hashlib.sha256((COMMON/'primitive_maps.json').read_bytes()).hexdigest(),'placements':placements,'routing_count':len(routes),'routes':routes,'cell_count':len(board),'board':[[x,y,c]for(x,y),c in sorted(board.items())],'ownership':[[x,y,owners[x,y]]for x,y in sorted(board)],'cases':cases,**ports}
 (HERE/'copy_macro.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'cells':len(board),'routes':len(routes),'cases':[(c['initial_input'],c['prior_input_write'],c['logical_result'],c['phase_steps'])for c in cases]}))
if __name__=='__main__':main()
