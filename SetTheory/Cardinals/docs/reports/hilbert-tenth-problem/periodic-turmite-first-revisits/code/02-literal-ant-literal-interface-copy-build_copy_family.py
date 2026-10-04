#!/usr/bin/env python3
"""Five finite literal COPY patterns. Executes only own-script finite routing/simulation."""
if not __debug__: raise RuntimeError('Run without -O')
import collections,hashlib,importlib.util,itertools,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
COMMON=HERE.parent/'common'
sp=importlib.util.spec_from_file_location('own_router',COMMON/'geometry_kit.py');R=importlib.util.module_from_spec(sp);sp.loader.exec_module(R)
CAT=json.loads((COMMON/'primitive_maps.json').read_text())
def inv(s):return(s[2]%2)^((s[0]+s[1])%2)
def build(name,xx):
 board={};blocked=set();owners={};placements=[]
 defs=[('box','input',(100,50),0)]+[('box',f'output_{i}',(x,250),0)for i,x in enumerate(xx)]+[('cruceA','read_cross',(190,105),2),('cruceB','write_cross',(140,181),0),('union','merge',(41,108),3)]
 for gadget,label,offset,k in defs:
  cells=R.transformed(CAT[gadget]['cell_map'],offset,k);assert not(set(cells)&set(board))
  board.update(cells);owners.update({p:label for p in cells});xs=[p[0]for p in cells];ys=[p[1]for p in cells]
  blocked.update((x,y)for x in range(min(xs),max(xs)+1)for y in range(min(ys),max(ys)+1))
  placements.append({'gadget':gadget,'label':label,'offset':offset,'clockwise_quarter_turns':k})
 entry=(max(300,max(xx)+200),105,3);exit=(min(0,min(xx)-100),105,3)
 specs=[('enter',entry,(190,105,3),[entry[:2],(190,105)]),('read_input',(184,99,3),(103,59,0),[(184,99),(103,99),(103,59)]),('one_cross',(109,56,1),(190,99,3),[(109,56),(220,56),(220,99),(190,99)]),('between_crossings',(184,105,3),(140,181,1),[(184,105),(130,105),(130,181),(140,181)]),('write_output_0',(146,187,1),(xx[0]+2,250,2),[(146,187),(160,187),(160,220),(xx[0]+2,220),(xx[0]+2,250)])]
 for i,(a,b) in enumerate(zip(xx,xx[1:])):
  specs.append((f'write_chain_{i}_{i+1}',(a+7,249,0),(b+2,250,2),[(a+7,249),(a+7,230),(b+2,230),(b+2,250)]))
 far=max(190,xx[-1]+90)
 specs += [('after_last_write',(xx[-1]+7,249,0),(145,182,3),[(xx[-1]+7,249),(xx[-1]+7,230),(far,230),(far,182),(145,182)]),('written_merge',(140,188,2),(44,108,0),[(140,188),(140,210),(44,210),(44,108)]),('zero_merge',(99,56,3),(44,100,2),[(99,56),(44,56),(44,100)]),('leave',(40,105,3),exit,[(40,105),exit[:2]])]
 routes=[]
 for label,start,target,anchors in specs:
  assert inv(start)==inv(target)==0
  states,cells=R.route(start,target,anchors,blocked,board);assert not(set(cells)&(set(board)|blocked))
  board.update(cells);owners.update({p:label for p in cells});routes.append({'label':label,'start':start,'terminal':target,'coarse_corridor_anchors':anchors,'states':states,'cells':[[x,y,c]for(x,y),c in sorted(cells.items())]})
 ports={'entry':entry,'exit':exit,'input_write_entry':(102,50,2),'input_write_exit':(107,49,0)}
 for i,x in enumerate(xx):
  ports.update({f'output_{i}_read_entry':(x+3,259,0),f'output_{i}_zero_exit':(x-1,256,3),f'output_{i}_one_exit':(x+9,256,1)})
 cases=[];histories=[]
 for ci,(initial,written)in enumerate([(0,False),(1,False),(0,True)]):
  b=board.copy();traces=[];counts=collections.Counter();out=1 if written else initial
  if initial:
   for p in[(104,54),(105,54)]:b[p]=0
  if written:
   tr,c=R.run(b,ports['input_write_entry'],ports['input_write_exit']);traces.append(tr);counts.update(c)
  tr,c=R.run(b,entry,exit);traces.append(tr);counts.update(c)
  assert all(b[x+4,254]==b[x+5,254]==1-out for x in xx)
  premacro_end=b.copy();precounts=counts.copy();out_traces=[]
  for i in range(len(xx)):
   tr,c=R.run(b,ports[f'output_{i}_read_entry'],ports[f'output_{i}_{"one"if out else"zero"}_exit']);out_traces.append(tr);counts.update(c)
  assert max(counts.values())<=2
  events=[];event_ports={(190,105,3):('read_cross','FIRST'),(190,99,3):('read_cross','SECOND'),(140,181,1):('write_cross','FIRST'),(145,182,3):('write_cross','SECOND'),(44,100,2):('merge','RIGHT'),(44,108,0):('merge','LEFT'),(103,59,0):('input','READ')}
  event_ports.update({(x+2,250,2):(f'output_{i}','WRITE')for i,x in enumerate(xx)})
  for step,row in enumerate(traces[-1]):
   if tuple(row[:3])in event_ports:component,operation=event_ports[tuple(row[:3])];events.append({'step':step,'component':component,'operation':operation})
  cases.append({'initial_input':initial,'prior_input_write':written,'logical_results':[out]*len(xx),'pre_read_phase_steps':list(map(len,traces)),'pre_read_phase_traces':traces,'output_read_phase_traces':out_traces,'output_read_phase_steps':list(map(len,out_traces)),'macro_events':events,'max_aggregate_visits_after_all_reads':max(counts.values()),'twice_visited_cells_after_all_reads':[list(p)for p in sorted(counts)if counts[p]==2],'final_changed_cells_basis':'common_INIT0_board','final_changed_cells_after_all_reads':[[x,y,c]for(x,y),c in sorted(b.items())if board[x,y]!=c]})
  for k in range(len(xx)+1):
   for order in itertools.permutations(range(len(xx)),k):
    b=premacro_end.copy();cnt=precounts.copy();phase_traces=traces.copy()
    for i in order:
     tr,c=R.run(b,ports[f'output_{i}_read_entry'],ports[f'output_{i}_{"one"if out else"zero"}_exit']);assert tr==out_traces[i];cnt.update(c);phase_traces.append(tr)
    assert max(cnt.values())<=2
    histories.append({'input_case_index':ci,'output_read_order':order,'phase_steps':list(map(len,phase_traces)),'trace_sha256':hashlib.sha256(json.dumps(phase_traces,separators=(',',':')).encode()).hexdigest(),'max_aggregate_visits':max(cnt.values()),'phase_trace_references':[f'cases[{ci}].pre_read_phase_traces[{j}]'for j in range(len(traces))]+[f'cases[{ci}].output_read_phase_traces[{i}]'for i in order]})
 return {'name':name,'status':'PASS_FINITE_COPY_FAMILY_MEMBER_ONLY','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'input_box_offset':[100,50],'output_box_offsets':[[x,250]for x in xx],'uniform_candidate_column_spacing':300,'row_spacing':200,'placements':placements,'routes':routes,'ports':ports,'board':[[x,y,c]for(x,y),c in sorted(board.items())],'ownership':[[x,y,owners[x,y]]for x,y in sorted(board)],'cell_count':len(board),'cases':cases,'all_optional_read_histories':histories,'parity_invariant':0,'limitations':['Finite member only; no periodic universal atlas','Prior input WRITE, macro activation, and later output READ activations require external physical connections','All output boxes belong to this resource interface and must acquire a single owner in any glued network']}

def main():
 variants=[('copy',[100]),('moved_copy_left',[-200]),('moved_copy_right',[400]),('fanout2',[-200,100]),('fanout3',[-200,100,400])]
 for name,xx in variants:
  obj=build(name,xx);(HERE/f'{name}_family_member.json').write_text(json.dumps(obj,indent=2)+'\n');print(json.dumps({'name':name,'cells':obj['cell_count'],'routes':len(obj['routes']),'histories':len(obj['all_optional_read_histories']),'steps':[(c['pre_read_phase_steps'],c['output_read_phase_steps'])for c in obj['cases']]}),flush=True)
if __name__=='__main__':main()
