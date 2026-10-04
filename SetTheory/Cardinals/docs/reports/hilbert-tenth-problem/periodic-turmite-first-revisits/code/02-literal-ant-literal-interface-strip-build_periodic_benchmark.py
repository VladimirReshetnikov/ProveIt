#!/usr/bin/env python3
"""A literal periodic NAND/copy strip, deliberately nonuniversal.
Establishes real growing-layer composition and whole-trajectory visit accounting.
"""
if not __debug__:raise RuntimeError('Assertions required')
import collections,hashlib,itertools,json,pathlib,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'common'))
from geometry_kit import route
D=((0,-1),(1,0),(0,1),(-1,0));PERIOD=(1400,400)

def translated(rows,dx,dy):return{(x+dx,y+dy):c for x,y,c in rows}
def box_support(x,y,maps):return{(x+a,y+b)for a,b,c in maps['box']['cell_map']}
def main():
 nb=(ROOT/'nand/nand_macro.json').read_bytes();cb=(ROOT/'copy/normalized_copy.json').read_bytes()
 nand=json.loads(nb);copy=json.loads(cb);maps=json.loads((ROOT/'common/primitive_maps.json').read_text())
 components=[('NAND',translated(nand['board'],0,0)),('COPY_left',translated(copy['board'],0,200)),('COPY_right',translated(copy['board'],600,200))]
 board={};overlaps=[];owners={}
 allowed=box_support(100,250,maps)|box_support(700,250,maps)
 for name,cells in components:
  overlap=set(cells)&set(board)
  if overlap:
   assert overlap<=allowed and len(overlap)==43
   assert all(cells[p]==board[p]for p in overlap)
   overlaps.append({'component':name,'overlap':sorted(overlap),'allowed_shared_box':True})
  board.update(cells)
  for p in cells:owners.setdefault(p,[]).append(name)
 # Future body is a collision guard, not a second initialized source in the motif.
 future=translated(nand['board'],0,400)
 guard=set(board)|set(future)
 routes=[]
 for name,start,end,anchors in[
  ('right_turn',(1200,75,1),(1200,305,3),[(1200,75),(1260,75),(1260,305),(1200,305)]),
  ('left_turn',(0,305,3),(0,475,1),[(0,305),(-60,305),(-60,475),(0,475)]),
 ]:
  states,cells=route(start,end,anchors,guard,board)
  assert not(set(cells)&set(board));assert not(set(cells)&set(future)),name
  board.update(cells);guard.update(cells)
  routes.append({'name':name,'start':start,'terminal':end,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 # Literal adjacent-translation census. Only same-box vertical aliases allowed.
 neighbor=[]
 for a,b in itertools.product(range(-2,3),repeat=2):
  if(a,b)==(0,0):continue
  trans={(x+a*PERIOD[0],y+b*PERIOD[1]):c for(x,y),c in board.items()}
  common=set(board)&set(trans)
  if common:
   assert a==0 and abs(b)==1
   target=(box_support(100,450,maps)|box_support(700,450,maps))if b==1 else(box_support(100,50,maps)|box_support(700,50,maps))
   assert common==target
   assert all(board[p]==trans[p]for p in common)
  neighbor.append({'dx_periods':a,'dy_periods':b,'overlap_cells':len(common)})
 xs=[p[0]for p in board];ys=[p[1]for p in board]
 assert max(xs)-min(xs)<PERIOD[0] and max(ys)-min(ys)<2*PERIOD[1]
 # Modulo painting is consistent, including inter-cycle shared boxes.
 tile={}
 for(x,y),c in board.items():
  p=x%PERIOD[0],y%PERIOD[1]
  assert p not in tile or tile[p]==c;tile[p]=c
 pins=[]
 for p,q in itertools.product([0,1],repeat=2):
  for cycles in [1,2,3,5]:
   changes={};visits=collections.Counter();s=(0,75,1);trace=[];checkpoints=[]
   for bit,x in[(p,100),(q,700)]:
    if bit:changes[x+4,54]=changes[x+5,54]=0
   want=(0,75+400*cycles,1);logical=[p,q]
   while s!=want:
    x,y,h=s;old=changes.get((x,y),tile.get((x%1400,y%400),0))
    hh=(h+(1 if old==0 else-1))%4;changes[x,y]=old^1;visits[x,y]+=1
    assert visits[x,y]<=2,('third visit',p,q,cycles,s)
    xx,yy=D[hh];ns=(x+xx,y+yy,hh);trace.append([x,y,h,old,*ns]);s=ns
    if len(trace)>150000:raise ValueError('benchmark run too long')
    if s[0]==0 and s[2]==1 and(s[1]-75)%400==0:
     j=(s[1]-75)//400;logical=[1-logical[0]*logical[1],0]
     bits=[]
     for bx in[100,700]:
      vals=[changes.get((bx+d,54+400*j),tile.get(((bx+d)%1400,(54+400*j)%400),0))for d in[4,5]]
      assert vals[0]==vals[1];bits.append(1-vals[0])
     assert bits==logical,(p,q,cycles,j,bits,logical,len(trace),s);checkpoints.append({'cycle':j,'logical':bits,'step':len(trace)})
   pins.append({'input':[p,q],'cycles':cycles,'departures':len(trace),'max_visits':max(visits.values()),
      'checkpoints':checkpoints,'trace_sha256':hashlib.sha256(json.dumps(trace,separators=(',',':')).encode()).hexdigest()})
 result={'status':'PASS_NONUNIVERSAL_LITERAL_PERIODIC_BENCHMARK','scope':'The map is (p,q)->(NAND(p,q),0); no universal CA or halting interface claimed.',
  'period':PERIOD,'start':[0,75,1],'input_one_changes':{'p':[[104,54,0],[105,54,0]],'q':[[704,54,0],[705,54,0]]},
  'component_source_pins':{'nand':hashlib.sha256(nb).hexdigest(),'copy':hashlib.sha256(cb).hexdigest()},
  'component_placements':[{'name':'NAND','offset':[0,0]},{'name':'COPY_left','offset':[0,200]},{'name':'COPY_right','offset':[600,200]}],
  'right_and_left_turn_routes':routes,'macro_overlaps':overlaps,'neighbor_census':neighbor,'motif_bounds':[min(xs),min(ys),max(xs),max(ys)],
  'motif_owned_cells':len(board),'periodic_owned_cells':len(tile),'periodic_black_cells':sum(tile.values()),
  'tile_specified_cells':[[x,y,c]for(x,y),c in sorted(tile.items())],'unowned_background_color':0,
  'finite_runs':pins,'whole_trajectory_proof':'For each downward cycle, new nonbox cells are fresh by the exact translation census. Only two output/input box supports alias adjacent cycles. Their merged histories are optional WRITE then at most one READ, separately certified including full post-WRITE board. Within a cycle the NAND and two COPY pieces share exactly their two connecting memory boxes. The actual right and left connectors link all control exits to the next entries, and the horizontal COPY seam is exact. Induction gives every cycle and all its prefixes, never entering unowned background cells; each physical resource cell is processed at most twice for the entire infinite trajectory. This uses the exhaustive local macro histories, not the finite runs as its general proof.',
  'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
 (ROOT/'strip/periodic_benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'period':PERIOD,'owned_cells':len(tile),'neighbor_checks':len(neighbor),'finite_runs':len(pins),'max_visits':2}))
if __name__=='__main__':main()
