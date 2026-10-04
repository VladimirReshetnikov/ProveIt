"""Own finite JSON-map boundary comparisons, no upstream execution or schedule decoding."""
from scan_motifs import maps,shift,union,black,stat,overlap,delta
import json
H=union(maps['NOT'],shift(maps['COPY'],0,200))
C=shift(maps['COPY'],0,200)
D=maps['DELAY']
result={'header':stat(H),'header_vs_delay':delta(H,D),'header_no_not':stat(C),'header_no_not_vs_delay':delta(C,D),'header_internal_overlap':overlap(maps['NOT'],C),'named_overlaps':{},'boundary_table':{},'right_marker_vs_header':delta(maps['RIGHT_MARKER'],H),'left_marker_vs_copy':delta(maps['LEFT_MARKER'],C)}
def add(label,a,b):
 o=overlap(a,b)
 if o['cells']:result['named_overlaps'][label]=o
for key,A in [('DELAY',D),('HEADER',H),('HEADER_NO_NOT',C),('NOT',maps['NOT']),('COPY200',C),('RIGHT_MARKER',maps['RIGHT_MARKER']),('LEFT_MARKER',maps['LEFT_MARKER']),('DUP',maps['DUP']),('MOVE_LEFT',maps['MOVE_LEFT']),('MOVE_RIGHT',maps['MOVE_RIGHT']),('NAND',maps['NAND'])]:
 for turn in ['LEFT_TURN','RIGHT_TURN']:
  for dx in [-1200,-600,0,600,1200]:
   for dy in [-400,0,400]:add(f'{key}/{turn}@{dx},{dy}',A,shift(maps[turn],dx,dy))
for key in ['RIGHT_MARKER','LEFT_MARKER']:
 for other,B in [('HEADER',H),('NOT',maps['NOT']),('COPY200',C),('DELAY',D),('RIGHT_MARKER',maps['RIGHT_MARKER']),('LEFT_MARKER',maps['LEFT_MARKER'])]:
  for dx in [-600,0,600]:
   for dy in [-400,0,400]:
    if dx==0 and dy==0:continue
    add(f'{key}/{other}@{dx},{dy}',maps[key],shift(B,dx,dy))
for turn in ['LEFT_TURN','RIGHT_TURN']:
 add(f'{turn}/{turn}@0,400',maps[turn],shift(maps[turn],0,400))
# Normal routing coordinates relative to e=right, choose symbolic F=4000,
# safely larger than all finite-map extents; no schedule instantiated.
F=4000
routes={
 'bottom_east':{(a,F+75+b-1):b for a in range(170) for b in [0,1]},
 'up_bottom':{(175+b-1,F+69-a):b for a in range(800) for b in [0,1]},
 'up_top':{(175+b-1,80+a):b for a in range(800) for b in [0,1]},
 'top_east':{(180+a,75+b-1):b for a in range(1020) for b in [0,1]},
 'corner_EN':shift(maps['CORNER_EN'],170,F+70),
 'corner_NE':shift(maps['CORNER_NE'],174,79),
 'footer_left_COPY':shift(maps['COPY'],-600,F+200),
 'footer_right_COPY':shift(maps['COPY'],0,F+200),
 'footer_left_NOT':shift(maps['NOT'],-600,F),
 'last_right_turn':shift(maps['RIGHT_TURN'],0,F-400),
 'first_right_turn':maps['RIGHT_TURN'],
 'next_header_NOT':shift(maps['NOT'],1200),
 'next_header_COPY':shift(C,1200),
}
result['route_maps']={k:stat(v) for k,v in routes.items()}
result['route_overlaps']={}
items=list(routes.items())
for j,(a,A) in enumerate(items):
 for b,B in items[j+1:]:
  o=overlap(A,B)
  if o['cells']:result['route_overlaps'][a+'/'+b]=o
# Vertical macro neighbor footer-to-header has j staggering S/2; both are multiples of 600.
# Footer H/C+special marker reaches V+259, next header starts V+50.
for a,A in [('HEADER',H),('COPY200',C),('RIGHT_MARKER',maps['RIGHT_MARKER']),('LEFT_MARKER',maps['LEFT_MARKER'])]:
 for b,B in [('HEADER',H),('HEADER_NO_NOT',C)]:
  for dx in [-600,0,600]:add(f'footer_{a}/next_macro_{b}@{dx},400',A,shift(B,dx,400))
print(json.dumps(result,indent=2))
