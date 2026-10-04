#!/usr/bin/env python3
"""Literal random-access coloring of the proposed fixed U15 ant atlas.
Uses exact finite templates and an exact finite compressed program, never a dense bitmap.
Callers must consult the final gate receipt; this file alone is not a correctness claim.
"""
if not __debug__:raise RuntimeError('Assertions required')
import hashlib,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ca'))
from physical_program import row_at
D=((0,-1),(1,0),(0,1),(-1,0))
def read(rel):return json.loads((ROOT/rel).read_text())
def board(a):return{(x,y):c for x,y,c in a['board']}
def rot(p,k):
 x,y=p
 for _ in range(k%4):x,y=-y,x
 return x,y
class Atlas:
 def __init__(self):
  self.program=read('ca/physical_program.json');p=self.program
  self.R=p['program_rows'];self.W=p['tile_slots'];self.K=p['active_columns'];self.S=p['CA_macro_width'];self.V=p['CA_macro_height'];self.F=400*(self.R+1)
  self.left=600;self.right=600*(self.W-1)
  self.header_marker=1+12*p['selected_slot_stride'];self.right_marker=1+23*p['selected_slot_stride']
  self.maps={}
  for key,rel in [('NOT','not/normalized_not.json'),('COPY','copy/normalized_copy.json'),('DELAY','copy/delayed_copy.json'),
      ('DUP','copy/pair_dup.json'),('MOVE_LEFT','copy/pair_move_left.json'),('MOVE_RIGHT','copy/pair_move_right.json'),
      ('RIGHT_MARKER','copy/marker_right_stop.json'),('LEFT_MARKER','copy/marker_left_start.json')]:self.maps[key]=board(read(rel))
  a=board(read('nand/nand_macro.json'))
  for dx in[0,600]:
   for(x,y),c in self.maps['COPY'].items():
    q=x+dx,y+200;assert q not in a or a[q]==c;a[q]=c
  self.maps['NAND']=a
  strip=read('strip/periodic_benchmark.json')
  self.maps['RIGHT_TURN']={(x-1200,y):c for x,y,c in strip['right_and_left_turn_routes'][0]['cells']}
  self.maps['LEFT_TURN']={(x,y):c for x,y,c in strip['right_and_left_turn_routes'][1]['cells']}
  primitives=read('common/primitive_maps.json')
  self.maps['CORNER_EN']={(x,y):c for x,y,c in primitives['cable_c']['cell_map']}
  self.maps['CORNER_NE']={rot((x,y),3):c for x,y,c in primitives['cable_b']['cell_map']}
 def wire(self,x,y,start,h,length):
  k=(h-1)%4;a,b=rot((x-start[0],y-start[1]),-k);b+=1
  return b if 0<=a<length and b in[0,1]else None
 def paints(self,x,y):
  found=[]
  def add(key,lx,ly,label):
   value=self.maps[key].get((lx,ly))
   if value is not None:found.append((label,value))
  j0=y//self.V
  for j in[j0-1,j0,j0+1]:
   Y=y-j*self.V
   if not(50<=Y<=self.V+259):continue
   shift=(j%2)*(self.S//2);i0=(x-shift)//self.S
   for i in[i0-1,i0,i0+1]:
    X=x-(i*self.S+shift)
    if not(0<=X<=self.S+600):continue
    origin=(j,i)
    # Full header/internal rounds, including all vertical boundary candidates.
    r0=(Y-50)//400
    for r in[r0-1,r0,r0+1]:
     if not(0<=r<=self.R):continue
     yy=Y-400*r
     if 50<=yy<=459:
      k0=X//600
      if r==0:
       for k in[k0-1,k0]:
        if 1<=k<=self.W-2:
         if k!=self.header_marker:add('NOT',X-600*k,yy,('header_NOT',origin,k))
         add('COPY',X-600*k,yy-200,('header_COPY',origin,k))
      else:
       kind,pair=row_at(self.program,r-1);pk=pair+1
       add(kind,X-600*pk,yy,('program_pair',origin,r,pk,kind))
       for k in[k0-1,k0]:
        if 1<=k<=self.W-2 and k not in[pk,pk+1]:add('DELAY',X-600*k,yy,('program_delay',origin,r,k))
     add('RIGHT_TURN',X-self.right,yy,('right_turn',origin,r))
     add('LEFT_TURN',X-self.left,yy,('left_turn',origin,r))
    # Footer NOT row and the outer W-copy row; marker maps replace both relevant phases.
    yy=Y-self.F;k0=X//600
    if 50<=yy<=659:
     for k in[k0-1,k0]:
      if 1<=k<=self.W-2:
       if k==self.right_marker:add('RIGHT_MARKER',X-600*k,yy,('right_marker',origin,k))
       else:add('NOT',X-600*k,yy,('footer_NOT',origin,k))
      if 0<=k<self.W:
       if k==1:add('LEFT_MARKER',X-600*k,yy,('left_marker',origin,k))
       elif k!=self.right_marker:add('COPY',X-600*k,yy-200,('outer_COPY',origin,k))
    # A normal C exit rises on a dedicated margin channel, then joins next C's header.
    e=self.right;endY=self.F+75
    for name,start,h,length in[
      ('normal_bottom_east',(e,endY),1,170),
      ('normal_up',(e+175,endY-6),0,self.F-10),
      ('normal_top_east',(e+180,75),1,1020)]:
     value=self.wire(X,Y,start,h,length)
     if value is not None:found.append(((name,origin),value))
    add('CORNER_EN',X-(e+170),Y-(endY-5),('normal_corner_EN',origin))
    add('CORNER_NE',X-(e+174),Y-79,('normal_corner_NE',origin))
  return found
 def color(self,x,y):
  found=self.paints(x,y)
  if not found:return 0
  assert all(v==found[0][1]for label,v in found),(x,y,found)
  return found[0][1]
 def input_changes(self,left,right,anchor):
  assert all(b in[0,1]for b in list(left)+list(right))
  states=list(reversed(left))+[2]+list(right);m=len(states);changes={}
  for x,y,c in anchor:
   assert self.color(x,y)!=c;changes[x,y]=c
  def bit_box(module,slot):
   xx=module*self.S+600+600*(slot*self.program['selected_slot_stride'])
   for dx in[104,105]:
    q=xx+dx,54;assert self.color(*q)==1
    assert q not in changes or changes[q]==0;changes[q]=0
  bit_box(0,12);bit_box(m,11)
  for i,value in enumerate(states):
   for b in range(11):
    if(value>>b)&1:bit_box(i,13+b);bit_box(i+1,b)
  return[[x,y,c]for(x,y),c in sorted(changes.items())]
if __name__=='__main__':
 a=Atlas();print(json.dumps({'status':'COLOR_GENERATOR_PRESENT_REQUIRES_FINAL_GATE_REVIEW','horizontal_period':a.S,'vertical_period':2*a.V,'program_rows':a.R,'template_count':len(a.maps)}))
