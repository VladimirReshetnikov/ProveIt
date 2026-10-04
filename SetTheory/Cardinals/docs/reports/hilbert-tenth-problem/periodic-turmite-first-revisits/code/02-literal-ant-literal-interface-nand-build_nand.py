#!/usr/bin/env python3
"""Literal two-input NAND with exhaustive prior-write/input/output-read histories."""
if not __debug__:raise RuntimeError('Assertions required; do not use -O')
import collections,hashlib,itertools,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'common'))
from geometry_kit import transformed,route,run

def main():
 data=json.loads((ROOT/'common/primitive_maps.json').read_text());board={};blocked=set();owners={};placements=[]
 for name,label,offset,k in [('box','P',(100,50),0),('box','Q',(700,50),0),('box','O',(100,250),0),('box','ZERO_SLOT',(700,250),0),('cruceB','XP',(50,75),0),('cruceB','XQ',(650,75),0),('union','ZERO_MERGE',(105,125),2),('union','FINAL_MERGE',(1171,100),1)]:
  cells=transformed(data[name]['cell_map'],offset,k)
  assert not(set(cells)&set(board));board.update(cells);owners.update({p:label for p in cells})
  xs=[p[0]for p in cells];ys=[p[1]for p in cells]
  blocked.update((x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1))
  placements.append({'gadget':name,'label':label,'offset':offset,'clockwise_quarter_turns':k})
 specs=[
 ('enter',(0,75,1),(50,75,1),[(0,75),(50,75)]),
 ('read_P',(56,81,1),(103,59,0),[(56,81),(103,81),(103,59)]),
 ('P0_cross',(99,56,3),(55,76,3),[(99,56),(70,56),(70,76),(55,76)]),
 ('P1_to_Q',(109,56,1),(650,75,1),[(109,56),(600,56),(600,75),(650,75)]),
 ('read_Q',(656,81,1),(703,59,0),[(656,81),(703,81),(703,59)]),
 ('Q0_cross',(699,56,3),(655,76,3),[(699,56),(670,56),(670,76),(655,76)]),
 ('P0_merge',(50,82,2),(97,122,1),[(50,82),(50,122),(97,122)]),
 ('Q0_merge',(650,82,2),(105,122,3),[(650,82),(650,122),(105,122)]),
 ('write_O',(102,126,2),(102,250,2),[(102,126),(102,250)]),
 ('after_write',(107,249,0),(1168,108,0),[(107,249),(107,238),(1168,238),(1168,108)]),
 ('Q1_merge',(709,56,1),(1168,100,2),[(709,56),(1168,56),(1168,100)]),
 ('leave',(1172,103,1),(1200,75,1),[(1172,103),(1190,103),(1190,75),(1200,75)]),
 ]
 routes=[]
 for label,start,target,anchors in specs:
  states,cells=route(start,target,anchors,blocked,board)
  assert not(set(cells)&set(board))and not(set(cells)&blocked),label
  board.update(cells);owners.update({p:label for p in cells})
  routes.append({'label':label,'start':start,'terminal':target,'coarse_corridor_anchors':anchors,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 assert all(0<=x<1200 and 50<=y<=259 for x,y in board)
 cases=[]
 for ps,qs in itertools.product(['INIT0','INIT1','WRITE0'],repeat=2):
  writes=[n for n,s in [('P',ps),('Q',qs)]if s=='WRITE0']
  orders=list(itertools.permutations(writes))or[()]
  for order in orders:
   b=board.copy();traces=[];counts=collections.Counter();phase_names=[]
   for s,x in[(ps,100),(qs,700)]:
    if s=='INIT1':b[x+4,54]=b[x+5,54]=0
   for name in order:
    x=100 if name=='P'else 700
    rr,cc=run(b,(x+2,50,2),(x+7,49,0));traces.append(rr);counts.update(cc);phase_names.append(name+'_write')
   pp=0 if ps=='INIT0'else 1;qq=0 if qs=='INIT0'else 1;answer=1-pp*qq
   rr,cc=run(b,(0,75,1),(1200,75,1));traces.append(rr);counts.update(cc);phase_names.append('compute')
   assert b[104,254]==b[105,254]==1-answer
   rr,cc=run(b,(703,259,0),(699,256,3));traces.append(rr);counts.update(cc);phase_names.append('zero_slot_read')
   end=(109,256,1)if answer else(99,256,3)
   rr,cc=run(b,(103,259,0),end);traces.append(rr);counts.update(cc);phase_names.append('output_read')
   assert max(counts.values())<=2
   # Enforce exact resource operation order on full physical compute traces.
   projected={n:[]for n in ['XP','XQ','P','Q','O']}
   starts={(50,75,1):('XP','FIRST'),(55,76,3):('XP','SECOND'),(650,75,1):('XQ','FIRST'),(655,76,3):('XQ','SECOND'),
      (103,59,0):('P','READ'),(703,59,0):('Q','READ'),(102,250,2):('O','WRITE'),(103,259,0):('O','READ'),(102,50,2):('P','WRITE'),(702,50,2):('Q','WRITE')}
   for tr in traces:
    for row in tr:
     if tuple(row[:3])in starts:
      name,op=starts[tuple(row[:3])];projected[name].append(op)
   assert projected['XP']==(['FIRST','SECOND']if not pp else['FIRST'])
   assert projected['XQ']==([]if not pp else['FIRST','SECOND']if not qq else['FIRST'])
   assert projected['P']==(['WRITE']if ps=='WRITE0'else[])+['READ']
   assert projected['Q']==(['WRITE']if qs=='WRITE0'else[])+(['READ']if pp else[])
   assert projected['O']==(['WRITE']if answer else[])+['READ']
   cases.append({'P_status':ps,'Q_status':qs,'prior_write_order':order,'P':pp,'Q':qq,'result':answer,'phase_names':phase_names,'phase_steps':list(map(len,traces)),
     'traces':traces,'max_visits':max(counts.values()),'resource_operation_sequences':projected,
     'twice_visited_cells':[list(p)for p in sorted(counts)if counts[p]==2]})
 out={'status':'PASS_FINITE_NAND_ONLY','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
  'primitive_map_sha256':hashlib.sha256((ROOT/'common/primitive_maps.json').read_bytes()).hexdigest(),
  'placements':placements,'routes':routes,'board':[[x,y,c]for(x,y),c in sorted(board.items())],
  'cells':len(board),'column_pitch':600,'storage_row_step':200,'output_logical_map':'(NAND(P,Q),0)','entry':[0,75,1],'exit':[1200,75,1],
  'ports':{'P_write_entry':[102,50,2],'P_write_exit':[107,49,0],'Q_write_entry':[702,50,2],'Q_write_exit':[707,49,0],
    'O_read_entry':[103,259,0],'O_read0_exit':[99,256,3],'O_read1_exit':[109,256,1],'ZERO_read_entry':[703,259,0],'ZERO_read_exit':[699,256,3]},
  'cases':cases,'universal_periodic_atlas':False}
 (ROOT/'nand/nand_macro.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({'status':out['status'],'cells':len(board),'cases':len(cases),'routes':len(routes),'traces':sum(sum(c['phase_steps'])for c in cases)}))
if __name__=='__main__':main()
