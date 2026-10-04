#!/usr/bin/env python3
"""Construction-free vector replay of every delayed pair-instruction history."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,itertools,json,pathlib
from verify_copy_family import board,trace,rot,wire,CAT,D,inv
P=pathlib.Path(__file__).resolve().parent

def verify(name):
 path=P/f'pair_{name}.json';raw=path.read_bytes();o=json.loads(raw);base=board(o['board']);merged={};own={};rects=[]
 for pl in o['placements']:
  b={}
  for x,y,c in CAT[pl['gadget']]['cell_map']:
   xx,yy=rot(x,y,pl['clockwise_quarter_turns']);b[xx+pl['offset'][0],yy+pl['offset'][1]]=c
  assert not set(b)&set(merged);merged.update(b);own.update({p:pl['label']for p in b});xs=[p[0]for p in b];ys=[p[1]for p in b];rects.append({(x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1)})
 for rt in o['routes']:
  b=board(rt['cells']);assert not set(b)&set(merged);assert not any(set(b)&r for r in rects)
  cnt=collections.Counter();end,tr=trace(b.copy(),rt['start'],cnt);assert end==rt['terminal']and[t[:3]for t in tr]+[end]==rt['states'];assert max(cnt.values())==1
  merged.update(b);own.update({p:rt['label']for p in b})
 assert merged==base and len(base)==o['cell_count'];assert[[x,y,own[x,y]]for x,y in sorted(own)]==o['ownership']
 ports=o['ports'];sel=o['selected_input_index'];ignored=1-sel;s=600*sel;written=o['written_output_indices'];assert(sel,written)=={'dup':(0,[0,1]),'move_right':(0,[1]),'move_left':(1,[0])}[name]
 assert ports['forward_entry']==[0,75,1]and ports['forward_exit']==[1200,75,1]and ports['entry']==[1200,305,3]and ports['exit']==[0,305,3]
 assert all(inv(p)==0 for p in ports.values());assert all(0<=x<=1200 for x,y in base)
 assert all(tuple(ports[k][:2])in base for k in['entry','forward_entry']);assert all(tuple(ports[k][:2])not in base for k in['exit','forward_exit'])
 expected={(kinds,order)for kinds in itertools.product(['INIT0','INIT1','WRITE0'],repeat=2)for order in itertools.permutations([i for i,k in enumerate(kinds)if k=='WRITE0'])}
 assert{(tuple(c['input_kinds']),tuple(c['prior_write_order']))for c in o['cases']}==expected and len(o['cases'])==10
 assert{(h['input_case_index'],tuple(h['output_read_order']))for h in o['all_optional_read_histories']}=={(ci,ro)for ci in range(10)for k in range(3)for ro in itertools.permutations(range(2),k)}
 crossports={(34+s,75,1):('forward_zero','FIRST'),(39+s,76,3):('forward_zero','SECOND'),(94+s,75,1):('forward_read','FIRST'),(94+s,81,1):('forward_read','SECOND'),(220+s,81,1):('forward_one','FIRST'),(225+s,82,3):('forward_one','SECOND'),(190+s,305,3):('read_cross','FIRST'),(190+s,299,3):('read_cross','SECOND'),(140+s,381,1):('write_cross','FIRST'),(145+s,382,3):('write_cross','SECOND')}
 prefixes=0;receipts=[];ftr=[]
 for h in o['all_optional_read_histories']:
  ci=h['input_case_index'];c=o['cases'][ci];b=base.copy();cnt=collections.Counter();trs=[];events=collections.defaultdict(list);effective=[int(k!='INIT0')for k in c['input_kinds']];outputs=[effective[sel]if i in written else 0 for i in range(2)];prefixes+=1
  for i,k in enumerate(c['input_kinds']):
   if k=='INIT1':
    for p in[(104+600*i,54),(105+600*i,54)]:b[p]=0
  prephases=[(f'input_{i}_write_entry',f'input_{i}_write_exit')for i in c['prior_write_order']]+[('forward_entry','forward_exit'),('entry','exit')]
  assert[list(p)for p in prephases]==c['pre_read_phase_ports']
  phases=prephases+[(f'output_{i}_read_entry',f'output_{i}_{"one"if outputs[i]else"zero"}_exit')for i in h['output_read_order']]
  for a,z in phases:
   inputs_before={p:b[p]for p in base if own[p].startswith('input_')};ignored_before={p:b[p]for p in base if own[p]==f'input_{ignored}'}
   zero_before={p:b[p]for p in base if own[p]in[f'output_{i}'for i in range(2)if i not in written]}
   end,tr=trace(b,ports[a],cnt);assert end==ports[z];trs.append(tr);prefixes+=len(tr)
   if a=='forward_entry':assert inputs_before=={p:b[p]for p in inputs_before};ftr.append(tr)
   if a in['forward_entry','entry']:assert ignored_before=={p:b[p]for p in ignored_before};assert zero_before=={p:b[p]for p in zero_before}
   if a=='entry':assert all(b[104+600*i,454]==b[105+600*i,454]==1-outputs[i]for i in range(2));assert sum(row[:3]==[103+600*sel,59,0]for row in tr)==1;assert not any(own[row[0],row[1]]==f'input_{ignored}'for row in tr)
   for row in tr:
    if tuple(row[:3])in crossports:g,ev=crossports[tuple(row[:3])];events[g].append(ev)
  expectedtr=c['pre_read_phase_traces']+[c['output_read_phase_traces'][i]for i in h['output_read_order']]
  assert trs==expectedtr and list(map(len,trs))==h['phase_steps'];assert hashlib.sha256(json.dumps(trs,separators=(',',':')).encode()).hexdigest()==h['trace_sha256'];assert max(cnt.values())==h['max_aggregate_visits']<=2
  assert all(v in[['FIRST'],['FIRST','SECOND']]for v in events.values());assert events['forward_read']==['FIRST','SECOND'];assert events['forward_zero']==(['FIRST','SECOND']if effective[sel]==0 else['FIRST']);assert events['forward_one']==(['FIRST','SECOND']if effective[sel]else['FIRST']);assert c['logical_outputs']==outputs
  if h['output_read_order']==[0,1]:
   assert[list(p)for p in sorted(cnt)if cnt[p]==2]==c['twice_visited_cells_after_all_reads'];assert[[x,y,v]for(x,y),v in sorted(b.items())if base[x,y]!=v]==c['final_changed_cells_after_all_reads']
  receipts.append({'case':ci,'output_read_order':h['output_read_order'],'logical_outputs':outputs,'phase_steps':h['phase_steps'],'maximum':max(cnt.values()),'ordered_crosses':dict(events)})
 assert all(t==ftr[0]for t in ftr)
 stub_records=[];incoming={k for k in ports if k.endswith('_entry')or k=='entry'}
 for L in[2,16,144]:
  b0=base.copy();ext={}
  for k,state in ports.items():
   dx,dy=D[state[2]];start=[state[0]-L*dx,state[1]-L*dy,state[2]]if k in incoming else state;cells,end=wire(start,L);assert not set(cells)&set(b0),(name,k,L);b0.update(cells);ext[k]=start if k in incoming else end
  for ci,c in enumerate(o['cases']):
   b=b0.copy();cnt=collections.Counter();steps=[]
   for i,k in enumerate(c['input_kinds']):
    if k=='INIT1':
     for p in[(104+600*i,54),(105+600*i,54)]:b[p]=0
   phases=c['pre_read_phase_ports']+[(f'output_{i}_read_entry',f'output_{i}_{"one"if c["logical_outputs"][i]else"zero"}_exit')for i in range(2)]
   for a,z in phases:end,tr=trace(b,ext[a],cnt);assert end==ext[z];steps.append(len(tr))
   assert max(cnt.values())<=2;stub_records.append({'length':L,'case':ci,'phase_steps':steps,'maximum':max(cnt.values())})
 middle={(x+100+600*i,y+250):v for i in range(2)for x,y,v in CAT['box']['cell_map']};assert not set(middle)&set(base)
 return o,{'name':name,'status':'PASS_DATA_ONLY_PAIR_INSTRUCTION','json_sha256':hashlib.sha256(raw).hexdigest(),'cells':len(base),'input_cases':10,'optional_read_histories':50,'micro_prefix_instances_including_history_initials':prefixes,'histories':receipts,'stub_replays':stub_records,'all_even_external_stub_lengths_up_to144_disjoint_by_containment':True,'ignored_input_unchanged_by_both_compute_phases':True,'zero_output_box_unchanged_until_optional_read':True,'forward_trace_identical_in_every_case':True,'intermediate_boxes_100_250_and_700_250_disjoint':True}

def main():
 objects={};receipts=[]
 for name in['dup','move_right','move_left']:
  o,r=verify(name);objects[name]=o;receipts.append(r);print(json.dumps({k:r[k]for k in['name','status','cells','input_cases','optional_read_histories','micro_prefix_instances_including_history_initials']}),flush=True)
 d=json.loads((P/'delayed_copy.json').read_text());d['width']=600;objects['delayed_copy']=d
 adjacency=[]
 for left,right in itertools.product(objects,repeat=2):
  a,b=objects[left],objects[right];aa={(x,y)for x,y,c in a['board']};bb={(x+a['width'],y)for x,y,c in b['board']};assert not aa&bb
  assert a['ports']['forward_exit']==[a['width'],75,1]and b['ports']['forward_entry']==[0,75,1]
  assert a['ports']['entry']==[a['width'],305,3]and b['ports']['exit']==[0,305,3]
  adjacency.append({'left':left,'right':right,'translation':a['width'],'support_intersection_count':0,'E_seam':[a['width'],75,1],'W_seam':[a['width'],305,3]})
 result={'status':'PASS_FINITE_PAIR_INSTRUCTIONS_AND_ALL_LOCAL_NEIGHBOR_SEAMS','verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'members':receipts,'all16_ordered_neighbor_checks':adjacency,'scope':'Construction-free independent vector replay of three pair instructions, exact first-undefined exits, all150 optional-read histories,90 simultaneous-stub replays and every pair of pair-instruction/delayed-COPY neighbors. No physical turnaround or universal compiler inferred.'}
 (P/'pair_instruction_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
