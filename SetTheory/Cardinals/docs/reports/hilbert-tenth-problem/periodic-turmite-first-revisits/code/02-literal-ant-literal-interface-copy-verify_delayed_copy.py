#!/usr/bin/env python3
"""Independent construction-free verification of delayed-copy data."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,importlib.util,itertools,json,pathlib
from verify_copy_family import board,trace,rot,wire,CAT,D,inv
P=pathlib.Path(__file__).resolve().parent
from stub_geometry import corridor,intersects
def main():
 raw=(P/'delayed_copy.json').read_bytes();o=json.loads(raw);base=board(o['board']);merged={};own={};rects=[]
 for pl in o['placements']:
  b={}
  for x,y,c in CAT[pl['gadget']]['cell_map']:
   xx,yy=rot(x,y,pl['clockwise_quarter_turns']);b[xx+pl['offset'][0],yy+pl['offset'][1]]=c
  assert not set(b)&set(merged);merged.update(b);own.update({p:pl['label']for p in b});xs=[p[0]for p in b];ys=[p[1]for p in b];rects.append({(x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1)})
 for rt in o['routes']:
  b=board(rt['cells']);assert not set(b)&set(merged);assert not any(set(b)&r for r in rects)
  cnt=collections.Counter();end,tr=trace(b.copy(),rt['start'],cnt);assert end==rt['terminal']and[t[:3]for t in tr]+[end]==rt['states'];assert max(cnt.values())==1
  merged.update(b);own.update({p:rt['label']for p in b})
 assert merged==base and len(base)==o['cell_count']==5664;assert[[x,y,own[x,y]]for x,y in sorted(own)]==o['ownership']
 ports=o['ports'];expected={'forward_entry':[0,75,1],'forward_exit':[600,75,1],'entry':[600,305,3],'exit':[0,305,3],'input_write_entry':[102,50,2],'input_write_exit':[107,49,0],'output_read_entry':[103,459,0],'output_zero_exit':[99,456,3],'output_one_exit':[109,456,1]};assert ports==expected;assert all(inv(s)==0 for s in ports.values())
 assert{(c['initial_input'],c['prior_write_timing'],c['later_output_read'])for c in o['cases']}=={(initial,timing,read)for initial,timing in[(0,None),(1,None),(0,'before_forward'),(0,'after_forward')]for read in[False,True]}
 ep={(34,75,1):('forward_zero_cross','FIRST'),(39,76,3):('forward_zero_cross','SECOND'),(94,75,1):('forward_read_cross','FIRST'),(94,81,1):('forward_read_cross','SECOND'),(220,81,1):('forward_one_cross','FIRST'),(225,82,3):('forward_one_cross','SECOND'),(190,305,3):('read_cross','FIRST'),(190,299,3):('read_cross','SECOND'),(140,381,1):('write_cross','FIRST'),(145,382,3):('write_cross','SECOND')}
 cases=[];prefixes=0;forward_traces=[]
 for case in o['cases']:
  b=base.copy();cnt=collections.Counter();traces=[];events=collections.defaultdict(list);out=1 if case['prior_write_timing']else case['initial_input'];prefixes+=1
  if case['initial_input']:
   for p in[(104,54),(105,54)]:b[p]=0
  phases=[]
  if case['prior_write_timing']=='before_forward':phases.append(['input_write_entry','input_write_exit'])
  phases.append(['forward_entry','forward_exit'])
  if case['prior_write_timing']=='after_forward':phases.append(['input_write_entry','input_write_exit'])
  phases.append(['entry','exit'])
  if case['later_output_read']:phases.append(['output_read_entry','output_one_exit'if out else'output_zero_exit'])
  assert phases==case['phase_ports']
  for a,z in phases:
   input_before={p:b[p]for p in b if own[p]=='input'}
   end,tr=trace(b,ports[a],cnt);assert end==ports[z];traces.append(tr);prefixes+=len(tr)
   if a=='forward_entry':assert input_before=={p:b[p]for p in input_before};forward_traces.append(tr)
   if a=='entry':assert b[104,454]==b[105,454]==1-out
   for row in tr:
    if tuple(row[:3])in ep:g,ev=ep[tuple(row[:3])];events[g].append(ev)
  assert all(v in[['FIRST'],['FIRST','SECOND']]for v in events.values());assert events['forward_read_cross']==['FIRST','SECOND'];assert events['forward_zero_cross']==(['FIRST','SECOND']if out==0 else['FIRST']);assert events['forward_one_cross']==(['FIRST','SECOND']if out else['FIRST'])
  assert traces==case['phase_traces'];assert list(map(len,traces))==case['phase_steps'];assert max(cnt.values())==case['max_aggregate_visits']==2
  assert[list(p)for p in sorted(cnt)if cnt[p]==2]==case['twice_visited_cells'];assert[[x,y,c]for(x,y),c in sorted(b.items())if base[x,y]!=c]==case['final_changed_cells'];assert case['logical_result']==out
  cases.append({'initial_input':case['initial_input'],'prior_write_timing':case['prior_write_timing'],'later_output_read':case['later_output_read'],'logical_output':out,'phase_steps':case['phase_steps'],'ordered_cross_projections':dict(events),'max_aggregate':max(cnt.values())})
 assert all(t==forward_traces[0]for t in forward_traces)
 incoming={k for k in ports if k.endswith('_entry')or k=='entry'};rays={k:corridor(s,k in incoming)for k,s in ports.items()}
 for k,r in rays.items():assert not[p for p in base if intersects(r,[(p[0],p[0]),(p[1],p[1])])],k
 for a,b in itertools.combinations(rays,2):assert not intersects(rays[a],rays[b]),(a,b)
 records=[]
 for L in[2,4,8,16,64,144]:
  b0=base.copy();ext={}
  for k,s in ports.items():
   dx,dy=D[s[2]];start=[s[0]-L*dx,s[1]-L*dy,s[2]]if k in incoming else s;cells,end=wire(start,L);assert not set(cells)&set(b0);b0.update(cells);ext[k]=start if k in incoming else end
  for c in o['cases']:
   b=b0.copy();cnt=collections.Counter();steps=[]
   if c['initial_input']:
    for p in[(104,54),(105,54)]:b[p]=0
   for a,z in c['phase_ports']:end,tr=trace(b,ext[a],cnt);assert end==ext[z];steps.append(len(tr))
   records.append({'stub_length':L,'initial_input':c['initial_input'],'prior_write_timing':c['prior_write_timing'],'later_output_read':c['later_output_read'],'phase_steps':steps,'max_aggregate':max(cnt.values())})
 # Pairwise neighbor support and a genuinely composed two-tile E/W sweep.
 shifted={(x+600,y):c for(x,y),c in base.items()};assert not set(shifted)&set(base)
 paired=base|shifted;pair_receipts=[]
 for a,b in itertools.product([(0,False),(1,False),(0,True)],repeat=2):
  c=paired.copy();cnt=collections.Counter();steps=[]
  for i,(initial,written)in enumerate([a,b]):
   if initial:
    for x,y in[(104,54),(105,54)]:c[x+600*i,y]=0
   if written:
    end,tr=trace(c,[102+600*i,50,2],cnt);assert end==[107+600*i,49,0];steps.append(len(tr))
  end,tr=trace(c,[0,75,1],cnt);assert end==[1200,75,1];steps.append(len(tr))
  end,tr=trace(c,[1200,305,3],cnt);assert end==[0,305,3];steps.append(len(tr))
  for i,(initial,written)in enumerate([a,b]):
   out=1 if written else initial;assert c[104+600*i,454]==c[105+600*i,454]==1-out
   end,tr=trace(c,[103+600*i,459,0],cnt);assert end==([109+600*i,456,1]if out else[99+600*i,456,3]);steps.append(len(tr))
  assert max(cnt.values())<=2;pair_receipts.append({'left_input':a,'right_input':b,'phase_steps':steps,'max_aggregate':max(cnt.values())})
 # An optional intermediate-row INIT0 storage box at(100,250) is not touched by either pass.
 intermediate={(x+100,y+250):c for x,y,c in CAT['box']['cell_map']};assert not set(intermediate)&set(base)
 result={'status':'PASS_DATA_ONLY_DELAYED_COPY_AND_TWO_TILE_SWEEPS','json_sha256':hashlib.sha256(raw).hexdigest(),'verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'owned_cells':len(base),'histories':cases,'micro_prefix_instances_including_case_initials':prefixes,'forward_trace_identical_in_all_histories':True,'all_external_half_strips_pairwise_disjoint_and_miss_core':True,'arbitrary_even_length_stub_argument':'Each external half-strip is disjoint from every other half-strip and core; symbolic even-width strip traversal visits each strip cell once. Each port activates at most once, so any even length preserves aggregate bound2.','stub_replays':records,'neighbor_shift600_disjoint':True,'two_tile_sequential_physical_sweeps':pair_receipts,'intermediate_storage_box_100_250_support_disjoint':True,'limitations':['E and W sweeps remain separated phases requiring an external physical turnaround','Two tiles are not a proof for arbitrary rows or a universal compiler']}
 (P/'delayed_copy_receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in['status','owned_cells','micro_prefix_instances_including_case_initials','forward_trace_identical_in_all_histories','neighbor_shift600_disjoint','intermediate_storage_box_100_250_support_disjoint']}))
if __name__=='__main__':main()
