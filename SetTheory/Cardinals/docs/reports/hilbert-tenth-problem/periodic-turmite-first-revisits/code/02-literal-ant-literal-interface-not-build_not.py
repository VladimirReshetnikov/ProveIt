#!/usr/bin/env python3
"""New literal finite NOT macro. Research component, no universal atlas.
Pure standard library; reads upstream gadget maps as data only.
"""
if not __debug__: raise RuntimeError("Run without -O: assertions carry this research audit")
import collections,heapq,hashlib,json,pathlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
D=((0,-1),(1,0),(0,1),(-1,0))

def rotate(p,k):
 x,y=p
 for _ in range(k%4):x,y=-y,x
 return x,y

def transformed(cells,offset,k):
 return {(rotate((x,y),k)[0]+offset[0],rotate((x,y),k)[1]+offset[1]):c for x,y,c in cells}

def route(start,target,anchors,blocked,used):
 allowed=set()
 for (ax,ay),(bx,by) in zip(anchors,anchors[1:]):
  assert ax==bx or ay==by
  for x in range(min(ax,bx)-2,max(ax,bx)+3):
   for y in range(min(ay,by)-2,max(ay,by)+3):allowed.add((x,y))
 forbidden=set(blocked)|set(used)
 forbidden.discard(start[:2]);forbidden.discard(target[:2])
 seq=0;heap=[(0,0,seq,start)];best={start:0};prev={}
 while heap:
  _,g,_,state=heapq.heappop(heap)
  if g!=best[state]:continue
  if state==target:
   states=[state]
   while state!=start:state=prev[state];states.append(state)
   states.reverse();cells={}
   for a,b in zip(states,states[1:]):
    x,y,h=a;assert (x,y)not in cells,('revisited route',x,y)
    hh=b[2];turn=(hh-h)%4;assert turn in(1,3)
    cells[x,y]=0 if turn==1 else 1
   return states,cells
  x,y,h=state
  for turn in (1,-1):
   hh=(h+turn)%4;dx,dy=D[hh];ns=(x+dx,y+dy,hh);xy=ns[:2]
   if xy not in allowed or xy in forbidden:continue
   if xy==target[:2] and ns!=target:continue
   gg=g+1
   if gg<best.get(ns,10**9):
    best[ns]=gg;prev[ns]=state;seq+=1
    heur=abs(ns[0]-target[0])+abs(ns[1]-target[1])
    heapq.heappush(heap,(gg+heur,gg,seq,ns))
 raise ValueError(('routing failed',start,target))

def run(board,start,stop):
 rows=[];count=collections.Counter();s=start
 while s!=stop:
  x,y,h=s
  if (x,y)not in board:raise ValueError(('undefined',s,stop))
  if len(rows)>10000:raise ValueError('run too long')
  c=board[x,y];hh=(h+(1 if c==0 else -1))%4
  board[x,y]=c^1;count[x,y]+=1;dx,dy=D[hh];s=(x+dx,y+dy,hh)
  rows.append([x,y,h,c,*s])
 return rows,count

def main():
 data=json.loads((ROOT/'common/primitive_maps.json').read_text());board={};blocked=set();owners={};placements=[]
 for name,label,offset,k in [('box','input',(100,50),0),('box','output',(100,250),0),('cruceB','ordered_cross',(50,75),0),('union','merge',(511,100),1)]:
  cells=transformed(data[name]['cell_map'],offset,k)
  assert not(set(cells)&set(board));board.update(cells);owners.update({p:label for p in cells})
  xs=[p[0]for p in cells];ys=[p[1]for p in cells]
  blocked.update((x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1))
  placements.append({'gadget':name,'label':label,'offset':offset,'clockwise_quarter_turns':k})
 specs=[
 ('enter',(0,75,1),(50,75,1),[(0,75),(50,75)]),
 ('read_input',(56,81,1),(103,59,0),[(56,81),(103,81),(103,59)]),
 ('zero_cross',(99,56,3),(55,76,3),[(99,56),(70,56),(70,76),(55,76)]),
 ('write_output',(50,82,2),(102,250,2),[(50,82),(50,230),(102,230),(102,250)]),
 ('after_write',(107,249,0),(508,108,0),[(107,249),(107,220),(508,220),(508,108)]),
 ('one_merge',(109,56,1),(508,100,2),[(109,56),(508,56),(508,100)]),
 ('leave',(512,103,1),(600,75,1),[(512,103),(590,103),(590,75),(600,75)]),
 ]
 routes=[]
 for label,start,target,anchors in specs:
  states,cells=route(start,target,anchors,blocked,board)
  assert not(set(cells)&set(board)),('overlap',label)
  assert not(set(cells)&blocked),('reserved core overlap',label)
  board.update(cells);owners.update({p:label for p in cells})
  routes.append({'label':label,'start':start,'terminal':target,'coarse_corridor_anchors':anchors,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 assert all(0<=x<600 and 50<=y<=259 for x,y in board)
 cases=[]
 for initial,written in [(0,False),(1,False),(0,True)]:
  b=board.copy();allrows=[];counts=collections.Counter()
  if initial:
   for p in[(104,54),(105,54)]:assert b[p]==1;b[p]=0
  if written:
   r,c=run(b,(102,50,2),(107,49,0));allrows.append(r);counts.update(c)
  r,c=run(b,(0,75,1),(600,75,1));allrows.append(r);counts.update(c)
  output=1-initial if not written else 0
  assert b[104,254]==b[105,254]==1-output
  # Input state after read is consumed; output reader is a separate legal later activation.
  outport=(-1,6,3)if output==0 else(9,6,1)
  terminal=(100+outport[0],250+outport[1],outport[2])
  r,c=run(b,(103,259,0),terminal);allrows.append(r);counts.update(c)
  assert max(counts.values())<=2
  cases.append({'initial_input':initial,'prior_input_write':written,'logical_result':output,
   'phase_steps':list(map(len,allrows)),'max_aggregate_visits':max(counts.values()),
   'twice_visited_cells':[list(p)for p in sorted(counts)if counts[p]==2],
   'phase_traces':allrows,'final_changed_cells_basis':'common_INIT0_board','final_changed_cells':[[x,y,c]for(x,y),c in sorted(b.items())if board[x,y]!=c]})
 result={'status':'PASS_FINITE_NOT_MACRO_ONLY','scope':'Literal new NOT macro with input-write/read and output-write/read chronology. Does not provide universal circuit, row turnaround, periodic tile, or halting observable.',
   'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
   'placements':placements,'routing_count':len(routes),'routes':routes,
   'cell_count':len(board),'board':[[x,y,c]for(x,y),c in sorted(board.items())],
   'cases':cases,'entry':[0,75,1],'exit':[600,75,1],
   'input_write_entry':[102,50,2],'input_write_exit':[107,49,0],
   'output_read_entry':[103,259,0],'output_zero_exit':[99,256,3],'output_one_exit':[109,256,1]}
 (ROOT/'not/normalized_not.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'cells':len(board),'routes':len(routes),'cases':[(c['initial_input'],c['prior_input_write'],c['logical_result'],c['phase_steps'])for c in cases]}))
if __name__=='__main__':main()
