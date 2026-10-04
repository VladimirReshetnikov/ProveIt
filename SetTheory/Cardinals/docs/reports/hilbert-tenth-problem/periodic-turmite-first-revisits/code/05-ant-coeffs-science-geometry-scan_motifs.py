"""JSON-only finite map scan; never imports/executes upstream code or decodes schedules."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]/'data/recipe_assets'
def read(s): return json.loads((ROOT/s).read_text())
def board(s): return {(x,y):c for x,y,c in read(s)['board']}
def shift(d,dx=0,dy=0): return {(x+dx,y+dy):c for (x,y),c in d.items()}
def union(*ds):
 out={}; conflicts=[]
 for d in ds:
  for q,c in d.items():
   if q in out and out[q]!=c: conflicts.append(q)
   out[q]=c
 assert not conflicts, conflicts[:20]
 return out
maps={k:board(p) for k,p in {'NOT':'not/normalized_not.json','COPY':'copy/normalized_copy.json','DELAY':'copy/delayed_copy.json','DUP':'copy/pair_dup.json','MOVE_LEFT':'copy/pair_move_left.json','MOVE_RIGHT':'copy/pair_move_right.json','RIGHT_MARKER':'copy/marker_right_stop.json','LEFT_MARKER':'copy/marker_left_start.json','NAND_RAW':'nand/nand_macro.json'}.items()}
maps['NAND']=union(maps['NAND_RAW'],shift(maps['COPY'],0,200),shift(maps['COPY'],600,200))
strip=read('strip/periodic_benchmark.json')['right_and_left_turn_routes']
maps['RIGHT_TURN']={(x-1200,y):c for x,y,c in strip[0]['cells']}
maps['LEFT_TURN']={(x,y):c for x,y,c in strip[1]['cells']}
pr=read('common/primitive_maps.json')
maps['CORNER_EN']={(x,y):c for x,y,c in pr['cable_c']['cell_map']}
maps['CORNER_NE']={(y,-x):c for x,y,c in pr['cable_b']['cell_map']}
def black(d): return {q for q,c in d.items() if c==1}
def stat(d):
 return {'cells':len(d),'black':len(black(d)),'bbox':[min(x for x,y in d),max(x for x,y in d),min(y for x,y in d),max(y for x,y in d)]}
def overlap(a,b):
 qs=set(a)&set(b); bb=black(a)&black(b); bad={q for q in qs if a[q]!=b[q]}
 return {'cells':len(qs),'black':len(bb),'conflicts':len(bad),'black_bbox':None if not bb else [min(x for x,y in bb),max(x for x,y in bb),min(y for x,y in bb),max(y for x,y in bb)],'sample_black':sorted(bb)[:8],'sample_conflicts':sorted(bad)[:8]}
def delta(a,b):
 ap=black(a)-black(b); bp=black(b)-black(a)
 return {'plus':len(ap),'minus':len(bp),'plus_bbox':None if not ap else [min(x for x,y in ap),max(x for x,y in ap),min(y for x,y in ap),max(y for x,y in ap)],'minus_bbox':None if not bp else [min(x for x,y in bp),max(x for x,y in bp),min(y for x,y in bp),max(y for x,y in bp)]}
if __name__=='__main__':
 result={'maps':{k:stat(v) for k,v in maps.items()},'same_row':{},'vertical':{},'op_vs_delay':{}}
 names=['DELAY','DUP','MOVE_LEFT','MOVE_RIGHT','NAND']
 for a in names:
  for b in names:
   for dx in [-1800,-1200,-600,0,600,1200,1800]:
    o=overlap(maps[a],shift(maps[b],dx,400))
    if o['cells']:result['vertical'][f'{a}/{b}@({dx},400)']=o
 for a in names:
  for dx in [-1200,-600,600,1200,1800]:
   o=overlap(maps[a],shift(maps['DELAY'],dx))
   if o['cells']:result['same_row'][f'{a}/DELAY@{dx}']=o
 two=union(maps['DELAY'],shift(maps['DELAY'],600))
 result['two_delays']=stat(two)
 for a in names[1:]:result['op_vs_delay'][a]=delta(maps[a],two)
 print(json.dumps(result,indent=2))
