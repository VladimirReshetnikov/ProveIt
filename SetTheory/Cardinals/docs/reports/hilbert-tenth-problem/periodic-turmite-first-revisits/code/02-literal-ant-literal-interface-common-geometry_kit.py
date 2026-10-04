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

