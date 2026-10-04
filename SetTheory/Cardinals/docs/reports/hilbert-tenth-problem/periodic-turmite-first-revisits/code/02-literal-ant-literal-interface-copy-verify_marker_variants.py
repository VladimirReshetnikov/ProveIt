#!/usr/bin/env python3
"""Construction-free replay of exclusive marker branches and initialization anchor."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,itertools,json,pathlib
from verify_copy_family import board,trace,rot,wire,CAT,D,inv
from stub_geometry import corridor,intersects
P=pathlib.Path(__file__).resolve().parent
LOCAL={'box':{'WRITE':(2,0,2),'READ':(3,9,0)},'cruceA':{'FIRST':(0,0,1),'SECOND':(0,6,1)},'cruceB':{'FIRST':(0,0,1),'SECOND':(5,1,3)},'union':{'LEFT':(0,3,1),'RIGHT':(8,3,3)}}
def verify(name):
 raw=(P/f'marker_{name}.json').read_bytes();o=json.loads(raw);base=board(o['board']);merged={};own={};rects=[];resource_types={};ep={};alias_records=[]
 for pl in o['placements']:
  b={};off=pl['offset'];k=pl['clockwise_quarter_turns'];g=pl['gadget'];resource=f'box@{off[0]},{off[1]}'if g=='box'else pl['label'];resource_types[resource]=g
  for x,y,c in CAT[g]['cell_map']:
   xx,yy=rot(x,y,k);b[xx+off[0],yy+off[1]]=c
  ov=set(b)&set(merged)
  if ov:assert g=='box'and ov==set(b)and len(ov)==43 and all(b[p]==merged[p]for p in ov);alias_records.append({'offset':off,'cells':43})
  for p,v in b.items():
   if p not in merged:merged[p]=v;own[p]=pl['label']
  xs=[p[0]for p in b];ys=[p[1]for p in b];rects.append({(x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1)})
  for op,(x,y,h)in LOCAL[g].items():xx,yy=rot(x,y,k);state=(xx+off[0],yy+off[1],(h+k)%4);ev=(resource,op);assert state not in ep or ep[state]==ev;ep[state]=ev
 for rt in o['routes']:
  b=board(rt['cells']);assert not set(b)&set(merged);assert not any(set(b)&r for r in rects);cnt=collections.Counter();end,tr=trace(b.copy(),rt['start'],cnt);assert end==rt['terminal']and[t[:3]for t in tr]+[end]==rt['states'];assert max(cnt.values())==1
  merged.update(b);own.update({p:rt['label']for p in b})
 assert merged==base and len(base)==o['cell_count'];assert[[x,y,own[x,y]]for x,y in sorted(own)]==o['ownership'];assert len(alias_records)==1
 ports=o['ports'];assert all(inv(p)==0 for p in ports.values());assert all(0<=x<=600 for x,y in base)
 assert{(c['input_kind'],c['later_output_read'])for c in o['cases']}==set(itertools.product(['INIT0','INIT1','WRITE0'],[False,True]));iy=o['input_box_offset'][1];oy=o['output_box_offset'][1];receipts=[];prefixes=0
 for c in o['cases']:
  b=base.copy();cnt=collections.Counter();tt=[];events=collections.defaultdict(list);effective=int(c['input_kind']!='INIT0');result=1-effective;prefixes+=1
  if c['input_kind']=='INIT1':
   for p in[(104,iy+4),(105,iy+4)]:b[p]=0
  phases=[['input_write_entry','input_write_exit']]if c['input_kind']=='WRITE0'else[]
  if name=='right_stop':phases+= [['forward_entry','return_exit']]if effective==0 else[['forward_entry','forward_continue_exit'],['return_entry','return_exit']]
  else:phases+= [['return_entry','header_exit']]if effective==1 else[['return_entry','return_continue_exit'],['header_entry','header_exit']]
  if c['later_output_read']:phases+=[['output_read_entry','output_one_exit'if result else'output_zero_exit']]
  assert phases==c['phase_ports']
  for a,z in phases:
   end,tr=trace(b,ports[a],cnt);assert end==ports[z];tt.append(tr);prefixes+=len(tr)
   if z in['return_exit','header_exit']:assert b[104,oy+4]==b[105,oy+4]==1-result
   for row in tr:
    if tuple(row[:3])in ep:r,op=ep[tuple(row[:3])];events[r].append(op)
  assert tt==c['phase_traces']and list(map(len,tt))==c['phase_steps'];assert max(cnt.values())==c['max_aggregate_visits']<=2
  assert[list(p)for p in sorted(cnt)if cnt[p]==2]==c['twice_visited_cells'];assert[[x,y,v]for(x,y),v in sorted(b.items())if base[x,y]!=v]==c['final_changed_cells']
  for r,g in resource_types.items():
   ev=events[r]
   if g=='box':assert ev in[[],['WRITE'],['READ'],['WRITE','READ']],(name,r,ev)
   elif g in['cruceA','cruceB']:assert ev in[[],['FIRST'],['FIRST','SECOND']],(name,r,ev)
   else:assert ev in[[],['LEFT'],['RIGHT']],(name,r,ev)
  assert events['NOT.ordered_cross'][0]=='FIRST'and events['COPY.read_cross'][0]=='FIRST'
  if name=='right_stop':assert events['TURN_MERGE']==(['RIGHT']if effective==0 else['LEFT'])
  else:assert events['START_MERGE']==(['LEFT']if effective==1 else['RIGHT'])
  for rt in o['routes']:assert all(cnt[x,y]<=1 for x,y,v in rt['cells'])
  receipts.append({'input_kind':c['input_kind'],'later_output_read':c['later_output_read'],'phase_ports':phases,'phase_steps':list(map(len,tt)),'logical_output':result,'maximum':max(cnt.values()),'resource_history_projections':dict(events)})
 incoming={k for k in ports if k.endswith('_entry')};rays={k:corridor(s,k in incoming)for k,s in ports.items()}
 for k,r in rays.items():assert not[p for p in base if intersects(r,[(p[0],p[0]),(p[1],p[1])])],(name,k)
 for a,b in itertools.combinations(rays,2):assert not intersects(rays[a],rays[b]),(name,a,b)
 stub_replays=[]
 for L in[2,16,144]:
  b0=base.copy();ext={}
  for k,s in ports.items():dx,dy=D[s[2]];start=[s[0]-L*dx,s[1]-L*dy,s[2]]if k in incoming else s;cells,end=wire(start,L);assert not set(cells)&set(b0);b0.update(cells);ext[k]=start if k in incoming else end
  for c in o['cases']:
   b=b0.copy();cnt=collections.Counter();steps=[]
   if c['input_kind']=='INIT1':
    for p in[(104,iy+4),(105,iy+4)]:b[p]=0
   for a,z in c['phase_ports']:end,tr=trace(b,ext[a],cnt);assert end==ext[z];steps.append(len(tr))
   assert max(cnt.values())<=2;stub_replays.append({'length':L,'input_kind':c['input_kind'],'later_output_read':c['later_output_read'],'steps':steps,'maximum':max(cnt.values())})
 return{'name':name,'status':'PASS_JOINT_MARKER_RESOURCE_HISTORIES','json_sha256':hashlib.sha256(raw).hexdigest(),'owned_cells':len(base),'micro_prefix_instances_including_case_initials':prefixes,'cases':receipts,'aliases':alias_records,'external_half_strips_all_disjoint':True,'arbitrary_even_stub_lengths_valid':True,'stub_replays':stub_replays}

def main():
 receipts=[verify(n)for n in['right_stop','left_start']]
 raw=(P/'left_start_anchor.json').read_bytes();a=json.loads(raw);mark=json.loads((P/'marker_left_start.json').read_text());base=board(mark['board']);b=base.copy();cnt=collections.Counter()
 assert a['source_json_sha256']==hashlib.sha256((P/'marker_left_start.json').read_bytes()).hexdigest();assert a['virtual_prefix_source_setup']==[[104,254,0],[105,254,0]]
 for x,y,v in a['virtual_prefix_source_setup']:b[x,y]=v
 state=[600,305,3];rows=[]
 while state!=a['actual_start_state']:
  x,y,h=state;v=b[x,y];dx,dy=D[h];vx,vy=(-dy,dx)if v==0 else(dy,-dx);ns=[x+vx,y+vy,D.index((vx,vy))];rows.append(state+[v]+ns);cnt[x,y]+=1;assert cnt[x,y]<=2;b[x,y]=1-v;state=ns
 assert rows==a['virtual_prefix_trace']and len(rows)==a['virtual_prefix_steps'];assert cnt[tuple(a['actual_start_state'][:2])]==0;assert board(a['post_prefix_board'])==b
 assert[[x,y,v]for(x,y),v in sorted(b.items())if base[x,y]!=v]==a['changed_cells'];assert a['changed_cell_count']==len(a['changed_cells'])
 suffixcounts=collections.Counter();end,suffix=trace(b,a['actual_start_state'],suffixcounts);assert end==a['verified_suffix_exit']and suffix==a['verified_suffix_trace'];assert b[104,654]==b[105,654]==1
 cnt.update(suffixcounts);assert max(cnt.values())<=2;end,tr=trace(b,[103,659,0],cnt);assert end==[99,656,3]and max(cnt.values())<=2
 anchor={'status':'PASS_EXACT_CONSTANT_PREFIX_PATCH_AND_SUFFIX','json_sha256':hashlib.sha256(raw).hexdigest(),'start':a['actual_start_state'],'prefix_steps':len(rows),'suffix_steps':len(suffix),'changed_cells_including_INIT1_setup':len(a['changed_cells']),'endpoint_processed_by_prefix':False,'suffix_alone_maximum':max(suffixcounts.values()),'prefix_suffix_and_optional_READ_maximum':max(cnt.values())}
 out={'status':'PASS_FINITE_MARKER_VARIANTS_AND_INITIAL_ANCHOR','verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'markers':receipts,'initial_anchor':anchor,'scope':'Only the exclusive joint branch histories are legal. No ordinary header-INIT1 entry is substituted. The anchor is an explicitly disclosed finite initialization patch, not a claim the prefix physically ran.'}
 (P/'marker_variants_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'markers':[{k:r[k]for k in['name','owned_cells','micro_prefix_instances_including_case_initials']}for r in receipts],'initial_anchor':anchor}))
if __name__=='__main__':main()
