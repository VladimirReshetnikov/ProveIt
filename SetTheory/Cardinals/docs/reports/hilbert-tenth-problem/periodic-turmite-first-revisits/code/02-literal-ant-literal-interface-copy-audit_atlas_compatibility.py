#!/usr/bin/env python3
"""Finite atlas geometry and phase audit, reading all macro/turn records as data."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,itertools,json,pathlib
from verify_copy_family import CAT,board,trace,inv
P=pathlib.Path(__file__).resolve().parent;ROOT=P.parent
FILES=['not/normalized_not.json','nand/nand_macro.json','copy/normalized_copy.json','copy/delayed_copy.json','copy/pair_dup.json','copy/pair_move_right.json','copy/pair_move_left.json','strip/periodic_benchmark.json']
RAW={f:(ROOT/f).read_bytes()for f in FILES};J={f:json.loads(r)for f,r in RAW.items()};pins={f:hashlib.sha256(r).hexdigest()for f,r in RAW.items()};failures=[]
def shifted(b,dx,dy):return{(x+dx,y+dy):v for(x,y),v in b.items()}
def box_at(x,y):return{(x+a,y+b):c for a,b,c in CAT['box']['cell_map']}
def bb(s):return[min(x for x,y in s),min(y for x,y in s),max(x for x,y in s),max(y for x,y in s)]
def contacts(a,b):
 if not a or not b:return[],[]
 bx,by,BX,BY=bb(b);p4=set();p8=set()
 for x,y in a:
  if not(bx-1<=x<=BX+1 and by-1<=y<=BY+1):continue
  for dx in[-1,0,1]:
   for dy in[-1,0,1]:
    if not(dx or dy):continue
    q=(x+dx,y+dy)
    if q in b:
     pair=tuple(sorted(((x,y),q)));p8.add(pair)
     if abs(dx)+abs(dy)==1:p4.add(pair)
 return[[*a,*b]for a,b in sorted(p4)],[[*a,*b]for a,b in sorted(p8)]
def combine(name,parts,width):
 merged={};aliases=[]
 for fn,dx,dy,expected in parts:
  b=shifted(board(J[fn]['board']),dx,dy);ov=set(b)&set(merged);want=set().union(*(set(box_at(x,y))for x,y in expected))if expected else set()
  if ov!=want:failures.append({'kind':'internal_macro_overlap','name':name,'file':fn,'observed':sorted(ov),'expected':sorted(want)})
  conflicts=[list(p)for p in ov if b[p]!=merged[p]]
  if conflicts:failures.append({'kind':'initial_color_conflict','name':name,'cells':conflicts})
  aliases.append({'source':fn,'translation':[dx,dy],'allowed_storage_aliases':expected,'overlap_cells':len(ov)});merged.update(b)
 return{'name':name,'width':width,'board':merged,'input_count':width//600,'output_count':width//600,'ports':{'forward_entry':[0,75,1],'forward_exit':[width,75,1],'entry':[width,305,3],'exit':[0,305,3]},'internal_aliases':aliases}

def main():
 tiles={}
 tiles['NOT_PAIR']=combine('NOT_PAIR',[('not/normalized_not.json',0,0,[]),('copy/normalized_copy.json',0,200,[[100,250]])],600)
 tiles['NAND_PAIR']=combine('NAND_PAIR',[('nand/nand_macro.json',0,0,[]),('copy/normalized_copy.json',0,200,[[100,250]]),('copy/normalized_copy.json',600,200,[[700,250]])],1200)
 for name,fn in[('DELAYED_COPY','copy/delayed_copy.json'),('DUP','copy/pair_dup.json'),('MOVE_RIGHT','copy/pair_move_right.json'),('MOVE_LEFT','copy/pair_move_left.json')]:
  w=600 if name=='DELAYED_COPY'else 1200;tiles[name]=combine(name,[(fn,0,0,[])],w)
 for name,t in tiles.items():
  b=t['board'];assert all(0<=x<=t['width']for x,y in b)
  for p in t['ports'].values():assert inv(p)==0
  assert tuple(t['ports']['forward_entry'][:2])in b and tuple(t['ports']['entry'][:2])in b
  assert tuple(t['ports']['forward_exit'][:2])not in b and tuple(t['ports']['exit'][:2])not in b
  assert all(set(box_at(100+600*i,y))<=set(b)for i in range(t['input_count'])for y in[50,450])
 horizontal=[]
 for na,nb in itertools.product(tiles,repeat=2):
  a,b=tiles[na],tiles[nb];shift=a['width'];asup=set(a['board']);bsup=set(shifted(b['board'],shift,0));ov=asup&bsup;c4,c8=contacts(asup,bsup)
  if ov:failures.append({'kind':'horizontal_overlap','left':na,'right':nb,'cells':sorted(ov)})
  horizontal.append({'left':na,'right':nb,'translation':[shift,0],'overlap_cells':[list(p)for p in sorted(ov)],'E_seam':[shift,75,1],'W_seam':[shift,305,3],'contacts4':c4,'contacts8_including4':c8})
 vertical=[]
 for na,nb in itertools.product(tiles,repeat=2):
  a,b=tiles[na],tiles[nb]
  for dy in[-400,400]:
   for k in range(-b['width']//600-1,a['width']//600+2):
    dx=600*k;ba=a['board'];bz=shifted(b['board'],dx,dy);asup=set(ba);bsup=set(bz);ov=asup&bsup;shared=[];expected=set()
    for ya,yb in itertools.product([50,450],repeat=2):
     for i,j in itertools.product(range(a['input_count']),range(b['input_count'])):
      ax,ay=100+600*i,ya;bx,by=100+600*j+dx,yb+dy
      if(ax,ay)==(bx,by):shared.append([ax,ay]);expected.update(box_at(ax,ay))
    conflicts=[list(p)for p in sorted(ov)if ba[p]!=bz[p]]
    if ov!=expected or conflicts:failures.append({'kind':'vertical_alias_mismatch','A':na,'B':nb,'translation':[dx,dy],'unexpected_cells':sorted(ov-expected),'missing_cells':sorted(expected-ov),'color_conflicts':conflicts})
    c4,c8=contacts(asup,bsup);nonshared4=[p for p in c4 if not(tuple(p[:2])in expected and tuple(p[2:])in expected)];nonshared8=[p for p in c8 if not(tuple(p[:2])in expected and tuple(p[2:])in expected)]
    vertical.append({'A':na,'B':nb,'translation':[dx,dy],'shared_storage_box_offsets':shared,'overlap_cell_count':len(ov),'overlap_cells':[list(p)for p in sorted(ov)],'initial_color_conflicts':conflicts,'contacts4':c4,'contacts8_including4':c8,'contacts4_not_internal_to_alias':nonshared4,'contacts8_not_internal_to_alias':nonshared8})
 print(json.dumps({'horizontal_cases':len(horizontal),'vertical_cases':len(vertical),'incompatibilities':len(failures)}),flush=True)
 turns={r['name']:r for r in J['strip/periodic_benchmark.json']['right_and_left_turn_routes']};turn_receipts=[]
 for name,r in turns.items():
  cnt=collections.Counter();end,tr=trace(board(r['cells']),r['start'],cnt);assert end==r['terminal']and[t[:3]for t in tr]+[end]==r['states'];assert max(cnt.values())==1;turn_receipts.append({'name':name,'cells':len(r['cells']),'start':r['start'],'terminal':end,'maximum_departures':1,'standalone_trace_exact':True})
 edge_checks=[]
 for name,t in tiles.items():
  rt=turns['right_turn'];off=t['width']-1200;rb=shifted(board(rt['cells']),off,0);asup=set(t['board']);rset=set(rb);ov=asup&rset;c4,c8=contacts(asup,rset)
  if ov:failures.append({'kind':'right_turn_overlap','tile':name,'cells':sorted(ov)})
  assert [rt['start'][0]+off,*rt['start'][1:]]==t['ports']['forward_exit'];assert[rt['terminal'][0]+off,*rt['terminal'][1:]]==t['ports']['entry']
  edge_checks.append({'kind':'right','tile':name,'translation':[off,0],'overlap_cells':[list(p)for p in sorted(ov)],'entry_equals_E_exit':True,'exit_equals_W_entry':True,'contacts4':c4,'contacts8_including4':c8})
 for current,nxt in itertools.product(tiles,repeat=2):
  a,b=tiles[current],tiles[nxt];lb=board(turns['left_turn']['cells']);below=shifted(b['board'],0,400);ovcur=set(lb)&set(a['board']);ovnext=set(lb)&set(below)
  if ovcur or ovnext:failures.append({'kind':'left_turn_overlap','current':current,'next':nxt,'current_cells':sorted(ovcur),'next_cells':sorted(ovnext)})
  assert turns['left_turn']['start']==a['ports']['exit'];assert turns['left_turn']['terminal']==[0,475,1]
  a4,a8=contacts(set(lb),set(a['board']));b4,b8=contacts(set(lb),set(below));edge_checks.append({'kind':'left','current':current,'next':nxt,'overlap_current':[list(p)for p in sorted(ovcur)],'overlap_next':[list(p)for p in sorted(ovnext)],'entry_equals_W_exit':True,'exit_equals_next_E_entry':True,'current_contacts4':a4,'current_contacts8_including4':a8,'next_contacts4':b4,'next_contacts8_including4':b8})
 # Direct physical E -> right turn -> W execution for all six complete round modules.
 physical=[]
 for name,t in tiles.items():
  rb=shifted(board(turns['right_turn']['cells']),t['width']-1200,0);base=t['board']|rb;n=t['input_count']
  for kinds in itertools.product(['INIT0','INIT1','WRITE0'],repeat=n):
   for wo in itertools.permutations([i for i,k in enumerate(kinds)if k=='WRITE0']):
    b=base.copy();cnt=collections.Counter();phases=[];p=[int(k!='INIT0')for k in kinds]
    for i,k in enumerate(kinds):
     if k=='INIT1':
      for x,y in[(104+600*i,54),(105+600*i,54)]:b[x,y]=0
    for i in wo:end,tr=trace(b,[102+600*i,50,2],cnt);assert end==[107+600*i,49,0];phases.append(len(tr))
    end,tr=trace(b,[0,75,1],cnt);assert end==[0,305,3];phases.append(len(tr))
    want={'NOT_PAIR':[1-p[0]],'NAND_PAIR':[1-(p[0]*(p[1]if n==2 else 0)),0],'DELAYED_COPY':[p[0]],'DUP':[p[0],p[0]],'MOVE_RIGHT':[0,p[0]],'MOVE_LEFT':[(p[1]if n==2 else 0),0]}[name]
    assert all(b[104+600*i,454]==b[105+600*i,454]==1-want[i]for i in range(n))
    for i in range(n):end,tr=trace(b,[103+600*i,459,0],cnt);assert end==([109+600*i,456,1]if want[i]else[99+600*i,456,3]);phases.append(len(tr))
    assert max(cnt.values())<=2;physical.append({'tile':name,'input_kinds':kinds,'write_order':wo,'output_bits':want,'phase_steps':phases,'max_aggregate_visits':max(cnt.values())})
 lowlevel=[]
 eboards={'NOT':board(J['not/normalized_not.json']['board']),'NAND':board(J['nand/nand_macro.json']['board'])}
 for a,b in itertools.product(eboards,repeat=2):
  w=600 if a=='NOT'else 1200;aa=set(eboards[a]);bz=set(shifted(eboards[b],w,0));assert not aa&bz;c4,c8=contacts(aa,bz);lowlevel.append({'phase':'E','left':a,'right':b,'seam':[w,75,1],'contacts4':c4,'contacts8_including4':c8})
 cb=board(J['copy/normalized_copy.json']['board']);aa=set(cb);bz=set(shifted(cb,600,0));assert not aa&bz;c4,c8=contacts(aa,bz);lowlevel.append({'phase':'W','left':'COPY','right':'COPY','seam':[600,105,3],'contacts4':c4,'contacts8_including4':c8})
 stale={k:{'recorded':v,'current':pins['nand/nand_macro.json'if k=='nand'else'copy/normalized_copy.json']}for k,v in J['strip/periodic_benchmark.json']['component_source_pins'].items()if k in['nand','copy']and v!=pins['nand/nand_macro.json'if k=='nand'else'copy/normalized_copy.json']}
 out={'status':'PASS_FINITE_ATLAS_GEOMETRY_PHASE_COMPATIBILITY'if not failures else'FAIL_FINITE_ATLAS_COMPATIBILITY','source_pins':pins,'verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'tile_inventory':{name:{'width':t['width'],'owned_cells':len(t['board']),'bounds':bb(t['board']),'ports':t['ports'],'internal_aliases':t['internal_aliases']}for name,t in tiles.items()},'horizontal_neighbors':horizontal,'vertical_neighbors':vertical,'contact_definition':'Unique unordered physical cell pairs with one endpoint in each component, excluding identical cells;8-neighbor includes4-neighbor. Internal contacts within aliased shared boxes are included and also separated from other contacts.','outside_census_proof':'Supports lie in[0,width]x[50,459]. The enumerated horizontal multiples600 include one extra empty column on each side; beyond these offsets there is neither overlap nor8-neighbor contact. Vertical offsets magnitude≥800 have at least391 rows between supports, hence no overlap/contact. dy=0 horizontal adjacency is checked for all ordered tile types.','turn_templates':turn_receipts,'edge_turn_checks':edge_checks,'continuous_E_turn_W_rounds':physical,'low_level_seams':lowlevel,'stale_strip_component_pins':stale,'incompatibilities':failures,'scope':'Finite geometry, exact ports/phase, canonical turns, full storage-box aliases and continuous one-round microtraces. Does not certify a particular full CA compiler, marker-specific header/footer turns, growing row packing or halting observable.'}
 (P/'atlas_compatibility_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'tile_types':len(tiles),'horizontal_neighbors':len(horizontal),'vertical_neighbors':len(vertical),'edge_turn_checks':len(edge_checks),'continuous_round_histories':len(physical),'incompatibilities':len(failures),'stale_strip_component_pins':stale}),flush=True)
if __name__=='__main__':main()
