#!/usr/bin/env python3
"""Data-only independent-vector replay; does not import any macro generator."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,itertools,json,pathlib
P=pathlib.Path(__file__).resolve().parent;COMMON=P.parent/'common'
CAT=json.loads((COMMON/'primitive_maps.json').read_text());D=((0,-1),(1,0),(0,1),(-1,0))
def rot(x,y,k):
 for _ in range(k):x,y=-y,x
 return x,y
def inv(s):return(s[2]%2)^((s[0]+s[1])%2)
def board(rows):
 b={}
 for x,y,c in rows:assert(x,y)not in b and c in[0,1];b[x,y]=c
 return b
def trace(b,entry,counts):
 s=list(entry);r=[]
 while tuple(s[:2])in b:
  assert len(r)<100000
  x,y,h=s;c=b[x,y];dx,dy=D[h];nx,ny=(-dy,dx)if c==0 else(dy,-dx)
  ns=[x+nx,y+ny,D.index((nx,ny))];assert inv(ns)==inv(s)==0
  b[x,y]=1-c;counts[x,y]+=1;assert counts[x,y]<=2
  r.append(s+[c]+ns);s=ns
 return s,r

def wire(s,n):
 x,y,h=s;k=(h-1)%4;rx,ry=rot(0,1,k);b={}
 for a in range(n):
  for z,c in[(0,0),(1,1)]:xx,yy=rot(a,z,k);b[xx+x-rx,yy+y-ry]=c
 dx,dy=D[h];return b,[x+n*dx,y+n*dy,h]

def verify(path):
 raw=path.read_bytes();o=json.loads(raw);base=board(o['board']);assert len(base)==o['cell_count'];merged={};own={};rects={}
 for pl in o['placements']:
  cells={}
  for x,y,c in CAT[pl['gadget']]['cell_map']:
   xx,yy=rot(x,y,pl['clockwise_quarter_turns']);cells[xx+pl['offset'][0],yy+pl['offset'][1]]=c
  assert not(set(cells)&set(merged));merged.update(cells);own.update({p:pl['label']for p in cells})
  xs=[p[0]for p in cells];ys=[p[1]for p in cells];rects[pl['label']]={(x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1)}
 for rt in o['routes']:
  b=board(rt['cells']);assert not(set(b)&set(merged));assert not any(set(b)&r for r in rects.values())
  c=collections.Counter();end,tr=trace(b.copy(),rt['start'],c);assert end==rt['terminal'];assert[t[:3]for t in tr]+[end]==rt['states'];assert max(c.values())==1
  merged.update(b);own.update({p:rt['label']for p in b})
 assert merged==base and[[x,y,own[x,y]]for x,y in sorted(own)]==o['ownership']
 ports=o['ports'];n=len(o['output_box_offsets']);W=o['horizontal_cell_domain'][1]
 assert ports['entry']==[W,105,3] and ports['exit']==[0,105,3];assert all(1<=x<=W for x,y in base)
 assert all(inv(s)==0 for s in ports.values());assert[(c['initial_input'],c['prior_input_write'])for c in o['cases']]==[(0,False),(1,False),(0,True)]
 ix,iy=o['input_box_offset'];inbits=[(ix+4,iy+4),(ix+5,iy+4)]
 expectedkeys={(ci,order)for ci in range(3)for k in range(n+1)for order in itertools.permutations(range(n),k)}
 assert{(h['input_case_index'],tuple(h['output_read_order']))for h in o['all_optional_read_histories']}==expectedkeys
 prefixes=0;receipts=[]
 for history in o['all_optional_read_histories']:
  ci=history['input_case_index'];case=o['cases'][ci];b=base.copy();counts=collections.Counter();traces=[];exits=[];steps=[];out=1 if case['prior_input_write']else case['initial_input'];prefixes+=1
  if case['initial_input']:
   for p in inbits:b[p]=0
  phases=[]
  if case['prior_input_write']:phases.append(('input_write_entry','input_write_exit'))
  phases.append(('entry','exit'))
  phases +=[(f'output_{i}_read_entry',f'output_{i}_{"one"if out else"zero"}_exit')for i in history['output_read_order']]
  for j,(a,z)in enumerate(phases):
   end,tr=trace(b,ports[a],counts);assert end==ports[z]
   traces.append(tr);steps.append(len(tr));exits.append(end);prefixes+=len(tr)
   if a=='entry':assert all(b[x+4,y+4]==b[x+5,y+4]==1-out for x,y in o['output_box_offsets'])
  expected=case['pre_read_phase_traces']+[case['output_read_phase_traces'][i]for i in history['output_read_order']]
  assert traces==expected and steps==history['phase_steps'];assert hashlib.sha256(json.dumps(traces,separators=(',',':')).encode()).hexdigest()==history['trace_sha256'];assert max(counts.values())==history['max_aggregate_visits']
  if history['output_read_order']==list(range(n)):
   assert[[x,y,c]for(x,y),c in sorted(b.items())if base[x,y]!=c]==case['final_changed_cells_after_all_reads'];assert[list(p)for p in sorted(counts)if counts[p]==2]==case['twice_visited_cells_after_all_reads']
  receipts.append({'case':ci,'read_order':history['output_read_order'],'steps':steps,'maximum':max(counts.values()),'first_undefined_exits':exits})
 # Build simultaneous 144-cell extensions on every external port, retaining explicit cell maps.
 # Every smaller positive even extension is contained in the same corridor; it shares no support.
 incoming={k for k in ports if k=='entry'or k.endswith('_entry')};stub_records=[];maxstubs={}
 for L in[2,4,8,16,64,144]:
  ext={};b0=base.copy();stubmaps={}
  for k,s in ports.items():
   dx,dy=D[s[2]];start=[s[0]-L*dx,s[1]-L*dy,s[2]]if k in incoming else s
   cells,end=wire(start,L);assert not(set(cells)&set(b0)),(path.name,k,L);b0.update(cells);ext[k]=start if k in incoming else end;stubmaps[k]=[[x,y,c]for(x,y),c in sorted(cells.items())]
  if L==144:maxstubs=stubmaps
  for ci,case in enumerate(o['cases']):
   b=b0.copy();cnt=collections.Counter();steps=[];out=1 if case['prior_input_write']else case['initial_input']
   if case['initial_input']:
    for p in inbits:b[p]=0
   phases=([('input_write_entry','input_write_exit')]if case['prior_input_write']else[])+[('entry','exit')]+[(f'output_{i}_read_entry',f'output_{i}_{"one"if out else"zero"}_exit')for i in range(n)]
   for a,z in phases:end,tr=trace(b,ext[a],cnt);assert end==ext[z];steps.append(len(tr))
   assert max(cnt.values())<=2;stub_records.append({'length':L,'input_case':ci,'phase_steps':steps,'max_aggregate':max(cnt.values())})
 return {'name':o['name'],'status':'PASS_DATA_ONLY_VECTOR_REPLAY','json_sha256':hashlib.sha256(raw).hexdigest(),'owned_cells':len(base),'components':len(o['placements'])+len(o['routes']),'optional_read_histories':len(receipts),'micro_prefix_instances_including_case_initials':prefixes,'all_expected_ports_parity':0,'replays':receipts,'stub_extension_replays':stub_records,'simultaneously_disjoint_stubs_up_to_even_length':144,'length144_stub_cells':maxstubs,'notes':['Every JSON route independently replayed to its first undefined cell','All legal ordered subsets of optional later output reads enumerated','Full input/macro/read phase traces are exactly checked','All positive even stub lengths≤144 are disjoint by containment; the canonical symbolic strip gives their exact traversal','Separated phases assume external connections and are not ant teleportations']}

def main():
 out=[]
 for name in['copy','moved_copy_left','moved_copy_right','fanout2','fanout3']:
  r=verify(P/f'normalized_{name}.json');out.append(r);print(json.dumps({k:r[k]for k in['name','status','owned_cells','optional_read_histories','micro_prefix_instances_including_case_initials']}),flush=True)
 (P/'independent_family_receipt.json').write_text(json.dumps({'status':'PASS_FINITE_FAMILY_ONLY','verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'members':out,'limitations':'No full instruction-row atlas, delayed-COPY tile, or universal compiler asserted'},indent=2)+'\n')
if __name__=='__main__':main()
