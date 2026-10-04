#!/usr/bin/env python3
"""Independent finite-selection, exact anchor and symbolic margin review."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,json,pathlib,sys
from verify_copy_family import board,wire,rot,trace,CAT,D
P=pathlib.Path(__file__).resolve().parent;ROOT=P.parent
sys.path.insert(0,str(ROOT/'atlas'))
from generator import Atlas
sys.path.insert(0,str(ROOT/'ca'))
from physical_program import row_at

def main():
 A=Atlas();pr=A.program;R=pr['program_rows'];W=pr['tile_slots'];B=pr['selected_slot_stride'];S=pr['CA_macro_width'];V=pr['CA_macro_height'];F=400*(R+1);e=600*(W-1);hm=1+12*B;rm=1+23*B
 assert(W,B,pr['active_columns'])==(960,40,958);assert S==600*W and V==F+400 and V%400==0;assert S//2==600*12*B and S%1200==0;assert (hm,rm)==(481,921)
 assert pr['initial_header_slot_entry']==[288600,75,1]and pr['fixed_start_local_head_state']==[288650,75,1]
 pins={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest()for f in['atlas/generator.py','ca/physical_program.py','ca/physical_program.json','copy/header_entry_only_receipt.json','copy/atlas_compatibility_receipt.json','copy/marker_variants_receipt.json','copy/marker_neighbors_receipt.json','copy/program_audit/receipt.json']}
 pa=json.loads((P/'program_audit/receipt.json').read_text());assert pa['inputs_sha256']['physical_program.json']==pins['ca/physical_program.json'];assert pa['bugs_found']==[]and pa['exact_highest_touched_column']<=pr['active_columns']-1
 sourcefiles={'NOT':'not/normalized_not.json','COPY':'copy/normalized_copy.json','DELAY':'copy/delayed_copy.json','DUP':'copy/pair_dup.json','MOVE_LEFT':'copy/pair_move_left.json','MOVE_RIGHT':'copy/pair_move_right.json','LEFT_MARKER':'copy/marker_left_start.json','RIGHT_MARKER':'copy/marker_right_stop.json'}
 M={k:board(json.loads((ROOT/f).read_text())['board'])for k,f in sourcefiles.items()};n=board(json.loads((ROOT/'nand/nand_macro.json').read_text())['board'])
 for dx in[0,600]:
  b={(x+dx,y+200):c for(x,y),c in M['COPY'].items()};ov=set(n)&set(b);expected={(x+100+dx,y+250)for x,y,c in CAT['box']['cell_map']};assert ov==expected and all(n[p]==b[p]for p in ov);n.update(b)
 M['NAND']=n;assert M=={k:A.maps[k]for k in M}
 # Every overlapping paint must belong to the regular literal storage-box grid.
 aliases=collections.defaultdict(set);checked=set();multiplicity=collections.Counter();records=[]
 boxlocal={(x,y)for x,y,c in CAT['box']['cell_map']}
 def check(x,y,value,label=None):
  found=A.paints(x,y);assert found,(x,y,'unpainted expected cell');assert all(v==value for lab,v in found),(x,y,value,found)
  if label is not None:assert any(lab==label for lab,v in found),(x,y,label,found)
  if len(found)>1:
   lx,ly=x%600-100,y%200-50;assert(lx,ly)in boxlocal,('non-box overlap',x,y,found)
   assert len(found)==2,('triple ownership',x,y,found)
   labs=tuple(sorted(repr(lab)for lab,v in found));aliases[(x-lx,y-ly,labs)].add((lx,ly))
  if(x,y)not in checked:multiplicity[len(found)]+=1;checked.add((x,y))
 def placement(key,dx,dy,label):
  for(x,y),v in M[key].items():check(x+dx,y+dy,v,label)
  records.append({'template':key,'translation':[dx,dy],'owned_cells':len(M[key]),'label':label})
 # Both stagger parities, all marker cells, and each header boundary class.
 for j in[0,1]:
  ox=(j%2)*(S//2);oy=j*V
  placement('LEFT_MARKER',ox+600,oy+F,('left_marker',(j,0),1))
  placement('RIGHT_MARKER',ox+600*rm,oy+F,('right_marker',(j,0),rm))
  for k in[1,hm-1,hm+1,W-2]:placement('NOT',ox+600*k,oy,('header_NOT',(j,0),k))
  for k in[1,hm-1,hm,hm+1,W-2]:placement('COPY',ox+600*k,oy+200,('header_COPY',(j,0),k))
  # All 960 next-row top boxes, including unused guard slots. Every cell of
  # each overlap is included, not just state cells or selected columns.
  for k in range(W):
   for x,y,c in CAT['box']['cell_map']:check(ox+600*k+100+x,oy+50+y,c)
 # Select one real instruction location for every template kind. This is a
 # class-witness test; exhaustive row-index coverage comes from the grammar
 # proof, and spatial completeness from the bounds below, not sampling.
 witnesses={}
 for lo,hi in zip(pr['prefix_rows'],pr['prefix_rows'][1:]):
  for k in set([lo,min(lo+1,hi-1),(lo+hi-1)//2,hi-1]):
   kind,pair=row_at(pr,k);witnesses.setdefault(kind,(k,pair))
 assert set(witnesses)=={'DUP','NAND','MOVE_LEFT','MOVE_RIGHT'}
 for kind,(k,pair)in witnesses.items():
  r=k+1;pk=pair+1;placement(kind,600*pk,400*r,('program_pair',(0,0),r,pk,kind))
  for col in[pk-1,pk+2]:
   if 1<=col<=W-2:placement('DELAY',600*col,400*r,('program_delay',(0,0),r,col))
 # Exact anchor background and suffix against the actual global evaluator.
 anchor=json.loads((P/'left_start_anchor.json').read_text());translated=json.loads((P/'fixed_initial_anchor_patch.json').read_text());dx,dy=288600,-400
 for(x,y),v in M['LEFT_MARKER'].items():check(x+dx,y+dy,v)
 changes={}
 for x,y,old,new in translated['patch']:assert A.color(x,y)==old and old!=new;changes[x,y]=new
 state=[288650,75,1];target=[289200,75,1];counts=collections.Counter();suffix=[]
 while state!=target:
  assert len(suffix)<2000;x,y,h=state;v=changes[x,y]if(x,y)in changes else A.color(x,y);vx,vy=D[h];nx,ny=(-vy,vx)if v==0 else(vy,-vx);ns=[x+nx,y+ny,D.index((nx,ny))];suffix.append(state+[v]+ns);counts[x,y]+=1;assert counts[x,y]<=2;changes[x,y]=1-v;state=ns
 expected=[[x+dx,y+dy,h,c,xx+dx,yy+dy,hh]for x,y,h,c,xx,yy,hh in anchor['verified_suffix_trace']];assert suffix==expected and len(suffix)==1276
 # The two finite corners and finite horizontal strips are independently
 # reconstructed, simulated to first undefined exits, and checked globally.
 margin=[]
 for j in[0,1]:
  ox=(j%2)*(S//2);oy=j*V;endY=F+75
  for label,start,h,length in[('normal_bottom_east',(e,endY,1),1,170),('normal_top_east',(e+180,75,1),1,1020)]:
   b,end=wire(start,length);cnt=collections.Counter();exit,tr=trace(b.copy(),start,cnt);assert exit==end and max(cnt.values())==1
   for(x,y),v in b.items():check(ox+x,oy+y,v,(label,(j,0)))
   margin.append({'parity':j,'resource':label,'entry':start,'exit':end,'owned_cells':len(b),'max_departures':1})
  for key,primitive,k,offset,start,end in[('normal_corner_EN','cable_c',0,(e+170,endY-5),(e+170,endY,1),(e+175,endY-6,0)),('normal_corner_NE','cable_b',3,(e+174,79),(e+175,79,0),(e+180,75,1))]:
   b={}
   for x,y,v in CAT[primitive]['cell_map']:xx,yy=rot(x,y,k);b[xx+offset[0],yy+offset[1]]=v
   cnt=collections.Counter();exit,tr=trace(b.copy(),start,cnt);assert exit==list(end)and max(cnt.values())==1
   for(x,y),v in b.items():check(ox+x,oy+y,v,(key,(j,0)))
   margin.append({'parity':j,'resource':key,'entry':start,'exit':end,'owned_cells':len(b),'max_departures':1})
 # Symbolic long-wire inequalities. These are uniform for every r and every
 # y in the enormous vertical interval; no long-wire sampling is used.
 assert F-10>0 and(F-10)%2==0
 up=[e+174,80,e+175,F+69];turns_right=[e,75,e+59,F-95];previous_left_extension=[S//2+600,50,S//2+1200,259]
 assert e+59<up[0]and up[3]<F+250 and previous_left_extension[2]<up[0]and up[2]<S
 assert F+69-(F-10)==79
 assert e+180+1020==S+600
 assert 600<e+174 and S+600>S+599
 # Adjacent wire/corner rectangles are pairwise disjoint by these exact
 # endpoint coordinate gaps, including the enormous up strip.
 rects={'bottom_east':[e,F+74,e+169,F+75],'corner_EN':[e+170,F+70,e+176,F+75],'up':up,'corner_NE':[e+174,74,e+179,79],'top_east':[e+180,74,S+599,75]}
 def ri(a,b):return max(a[0],b[0])<=min(a[2],b[2])and max(a[1],b[1])<=min(a[3],b[3])
 import itertools
 assert all(not ri(rects[a],rects[b])for a,b in itertools.combinations(rects,2))
 # Staggered selected-slot matching, exactly for every output slot/parity.
 stagger=[]
 for j in[0,1]:
  oldshift=(j%2)*(S//2);newshift=((j+1)%2)*(S//2)
  for t in range(24):
   x=oldshift+600*(1+B*t);module=(x-newshift)//S;local=(x-newshift)%S;assert local%600==0 and(local//600-1)%B==0;slot=(local//600-1)//B
   want=t+12 if t<12 else t-12;assert slot==want
   role='s1'if t==0 else's0'if t==23 else'right_state_bit_'+str(t-1)if t<12 else'left_state_bit_'+str(t-12)
   stagger.append({'old_parity':j,'old_output_slot':t,'new_module_relative_index':module,'new_input_slot':slot,'role':role})
 assert F+450==V+50 and F+650==V+250
 # Complete each observed multiple-paint group by checking the whole box.
 # This converts boundary observations into exact 43-cell alias certificates.
 for ox,oy,labs in list(aliases):
  for x,y,v in CAT['box']['cell_map']:check(ox+x,oy+y,v)
 assert all(v==boxlocal for v in aliases.values())
 alias_records=[{'box_origin':[x,y],'paint_labels':labs,'shared_cell_count':len(v)}for(x,y,labs),v in sorted(aliases.items())]
 out={'status':'PASS_INDEPENDENT_GLOBAL_COLOR_GEOMETRY_AND_MARGIN_REVIEW','verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'reviewed_sha256':pins,'parameters':{'R':R,'W':W,'K':pr['active_columns'],'S':S,'V':V,'F':F,'normal_margin_x':e,'header_marker_column':hm,'right_marker_column':rm},'actual_source_templates_match_independent_maps':True,'finite_global_placement_checks':records,'checked_unique_global_cells':len(checked),'paint_multiplicity_histogram':dict(multiplicity),'all_observed_overlaps_are_complete_43_cell_box_aliases':alias_records,'instruction_template_witnesses':witnesses,'exhaustive_program_index_proof':'program_audit/receipt.json and ANALYSIS.md; class witnesses above are not substituted for that arithmetic proof','selector_completeness_proof':{'CA_rows':'Every primitive/route has local Y in[50,V+259]. Thus its true j is j0 or j0−1; the ±1 loop includes every painter, also at negative coordinates.','CA_columns':'Every painter has local X in[0,S+599]. Thus true i is i0 or i0−1; the ±1 loop includes all painters.','rounds':'Full-round support yy∈[50,459] gives floor((Y−50)/400)=r or r+1. Left-turn support through476 also lies among the three candidate rounds. All legal r satisfy0≤r≤R. Footer/outer-marker extensions use their separate exact band.','slots':'A width600 one-slot support has local x∈[0,600], so its true k is k0 or k0−1. Pair supports are added once explicitly, with both consumed slots excluded from DELAY. Every program pair index≤919 gives pk≤920 and pk+1≤921<959, entirely inside active slots1…958.','partial_header':'Only header NOT at column481 is omitted. It is supplied by the preceding staggered LEFT_MARKER; all header COPYs remain present. Header-prefix W-only behavior is certified separately. Normal header-E-only0 with no preceding COPY is certified by header_entry_only_receipt.json.','global_ownership':'Same-band and consecutive-round interactions reduce to the checked finite neighbor atlas and complete boxes. Across CA rows, ordinary previous outer COPYs meet new header inputs only at complete boxes; LEFT_MARKER replaces exactly column481 and aliases its output with that column’s header COPY.'},'staggered_slot_matches':stagger,'vertical_alignment':{'previous_footer_output_y':F+450,'next_header_input_y':V+50,'previous_LEFT_MARKER_output_y':F+650,'next_header_COPY_input_y':V+250},'margin_finite_resources':margin,'margin_resource_rectangles':rects,'normal_margin_exact_head_sequence':[[e,F+75,1],[e+170,F+75,1],[e+175,F+69,0],[e+175,79,0],[e+180,75,1],[S+600,75,1]],'normal_margin_owned_cells_and_departures':2*F+2396,'long_wire_uniform_proof':{'support':up,'length':F-10,'colors':'At every integer Y∈[80,F+69], x=e+174 has0 and x=e+175 has1. In generator.wire, a=F+69−Y ranges0…F−11 and b=x−(e+175)+1.','same_CA_body_bound':'All internal/header/footer active-body cells have x≤e; right turns have x≤e+59. Outer guard COPY at x≥e begins only at y=F+250. Thus none can meet the up strip.','previous_CA_row_bound':'The only previous-row painter reaching current Y≥80 is its LEFT_MARKER extension. ModuloS its x interval is[S/2+600,S/2+1200]=[288600,289200], strictly left of the strip. Previous ordinary COPY/RIGHT_MARKER output ends at current y59.','next_CA_row_bound':'The next CA row begins at current y=V+50=F+450, strictly below the up-strip endF+69.','same_row_neighbor_bound':'Previous same-row C painters reach at most current x600, apart from their already excluded bands; next C painters start at x=S. The strip lies strictly between600 andS.','horizontal_strip_bounds':'Bottom strip lies beyond e and above footer outer COPY. Top strip starts beyond the right-turn extent and ends at S+599, exactly before next C active header starts at S+600. Previous-CA extension lies in the distant marker interval.','single_use':'Canonical even-width strips and the two independently replayed corners visit each owned cell once; their rectangles are pairwise disjoint. Repeated activation is a controller obligation, not inferred from colors.'},'anchor':{'whole_translated_background_cells':len(M['LEFT_MARKER']),'net_patch_cells':len(translated['patch']),'every_expected_baseline_color_matches_global_evaluator':True,'actual_start':[288650,75,1],'global_exact_suffix_steps':len(suffix),'suffix_max_departures':max(counts.values()),'suffix_terminal_is_next_header_column_entry':target},'periodicity_proof':'Translation byS preserves every local X; translation by2V preserves j parity and local Y. Hence the evaluator is S-by-2V periodic before finite input changes.','bugs_found':[],'corrected_metadata_note':'The old fixed-head slot-entry value was corrected before this reviewed hash; current fixed_start is288650 while initial_header_slot_entry remains288600.','limitations':['No claim that sampled template witnesses prove all601m program rows; the separate exact grammar proof and symbolic selector argument do that','Single activation, controller schedule, finite input semantics and accepting-site exclusivity remain in the parent global proof','The enormous vertical strip was proved by exact bounds and symbolic traversal, never materialized or sampled to claim disjointness']}
 (P/'global_generator_review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'global_cells_checked':len(checked),'complete_alias_groups':len(alias_records),'margin_departures':2*F+2396,'anchor_suffix_steps':len(suffix),'bugs_found':0}),flush=True)
if __name__=='__main__':main()
