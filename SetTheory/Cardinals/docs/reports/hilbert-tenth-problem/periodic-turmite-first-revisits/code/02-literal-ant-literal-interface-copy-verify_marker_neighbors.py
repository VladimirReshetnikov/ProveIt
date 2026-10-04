#!/usr/bin/env python3
"""Marker-neighbor/vertical alias audit plus skipped-E W-only header histories."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,itertools,json,pathlib
from verify_copy_family import board,trace,CAT
from audit_atlas_compatibility import contacts
P=pathlib.Path(__file__).resolve().parent;ROOT=P.parent
FILES={'NOT':ROOT/'not/normalized_not.json','COPY':P/'normalized_copy.json','RIGHT':P/'marker_right_stop.json','LEFT':P/'marker_left_start.json'}
RAW={n:p.read_bytes()for n,p in FILES.items()};J={n:json.loads(r)for n,r in RAW.items()};B={n:board(j['board'])for n,j in J.items()}
def shift(b,dx,dy):return{(x+dx,y+dy):v for(x,y),v in b.items()}
def bx(x,y):return{(x+a,y+b):v for a,b,v in CAT['box']['cell_map']}
def merge(a,b,boxoff):
 ov=set(a)&set(b);want=set().union(*(set(bx(x,y))for x,y in boxoff))if boxoff else set();assert ov==want;assert all(a[p]==b[p]for p in ov);return a|b

def main():
 neighbors=[]
 for marker,other,dy in[('RIGHT','NOT',0),('RIGHT','COPY',200),('LEFT','COPY',200),('LEFT','NOT',400)]:
  for dx in[-600,600]:
   a=B[marker];b=shift(B[other],dx,dy);assert not set(a)&set(b);c4,c8=contacts(set(a),set(b));neighbors.append({'marker':marker,'neighbor':other,'translation':[dx,dy],'overlap_cells':0,'contacts4':c4,'contacts8_including4':c8})
 vertical=[]
 for marker,other,dy,shared_y in[('RIGHT','NOT',400,450),('RIGHT','COPY',-200,50),('LEFT','NOT',0,250),('LEFT','COPY',600,650)]:
  for dx in[-600,0,600]:
   a=B[marker];b=shift(B[other],dx,dy);boxes=[[100,shared_y]]if dx==0 else[];merged=merge(a,b,boxes);c4,c8=contacts(set(a),set(b));vertical.append({'marker':marker,'resource':other,'translation':[dx,dy],'shared_boxes':boxes,'overlap_cell_count':len(set(a)&set(b)),'contacts4':c4,'contacts8_including4':c8})
 # W-only ordinary NOT_PAIR, because header E never visited this prefix column.
 np=merge(B['NOT'],shift(B['COPY'],0,200),[[100,250]]);wonly=[]
 old=set(bx(100,50))
 for kind in['INIT0','INIT1','WRITE0']:
  for read in[False,True]:
   b=np.copy();cnt=collections.Counter();trs=[];ports=[]
   if kind=='INIT1':
    for p in[(104,54),(105,54)]:b[p]=0
   if kind=='WRITE0':end,tr=trace(b,[102,50,2],cnt);assert end==[107,49,0];trs.append(tr);ports.append([[102,50,2],[107,49,0]])
   before={p:b[p]for p in old};end,tr=trace(b,[600,305,3],cnt);assert end==[0,305,3];assert not any(tuple(row[:2])in old for row in tr);trs.append(tr);ports.append([[600,305,3],[0,305,3]])
   assert before=={p:b[p]for p in old};assert b[104,454]==b[105,454]==1
   if read:end,tr=trace(b,[103,459,0],cnt);assert end==[99,456,3];trs.append(tr);ports.append([[103,459,0],[99,456,3]])
   assert max(cnt.values())<=2;wonly.append({'input_kind':kind,'later_output_read':read,'phase_states':ports,'phase_steps':list(map(len,trs)),'phase_traces':trs,'logical_output':0,'old_input_unchanged_by_W':True,'maximum':max(cnt.values()),'twice_visited_cells':[list(p)for p in sorted(cnt)if cnt[p]==2]})
 # A right-stop output really feeds the next normal header NOT; a left-start
 # header-NOT output really feeds the next header W-COPY. Full microtraces
 # enforce WRITE-before-READ at the aliased physical source box.
 extended=[]
 for name,other,dy,alias_y,laststart,lastexit,final_y in[('RIGHT','NOT',400,450,[0,475,1],[600,475,1],650),('LEFT','COPY',600,650,[600,705,3],[0,705,3],850)]:
  base=merge(B[name],shift(B[other],0,dy),[[100,alias_y]]);obj=J[name];iy=obj['input_box_offset'][1];ports=obj['ports']
  for kind in['INIT0','INIT1','WRITE0']:
   c=next(c for c in obj['cases']if c['input_kind']==kind and not c['later_output_read']);b=base.copy();cnt=collections.Counter();trs=[]
   if kind=='INIT1':
    for p in[(104,iy+4),(105,iy+4)]:b[p]=0
   for a,z in c['phase_ports']:end,tr=trace(b,ports[a],cnt);assert end==ports[z];trs.append(tr)
   end,tr=trace(b,laststart,cnt);assert end==lastexit;trs.append(tr)
   result=int(kind!='INIT0')if name=='RIGHT'else int(kind=='INIT0');assert b[104,final_y+4]==b[105,final_y+4]==1-result
   end,tr=trace(b,[103,final_y+9,0],cnt);assert end==([109,final_y+6,1]if result else[99,final_y+6,3]);trs.append(tr);assert max(cnt.values())<=2
   extended.append({'marker':name,'following_resource':other,'following_translation':[0,dy],'input_kind':kind,'final_output':result,'phase_steps':list(map(len,trs)),'trace_sha256':hashlib.sha256(json.dumps(trs,separators=(',',':')).encode()).hexdigest(),'maximum':max(cnt.values())})
 out={'status':'PASS_MARKER_NEIGHBORS_VERTICAL_ALIASES_AND_SKIPPED_HEADER_PREFIX','source_pins':{n:hashlib.sha256(r).hexdigest()for n,r in RAW.items()},'verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'horizontal_neighbors':neighbors,'vertical_interfaces':vertical,'W_only_NOT_PAIR_histories':wonly,'W_only_contract':'Upper E activation is skipped, not delayed. Old input may have INIT0/INIT1/priorWRITE0 but is never READ; W reads untouched intermediate INIT0 and leaves final output0. No later upper E activation is authorized by this history.','extended_marker_microtrace_cases':extended,'geometric_constants':{'column_pitch':600,'storage_row_step':200,'full_round_step':400,'extra_padding_required':False},'scope':'Local neighboring standard E-NOT/W-COPY columns and the stated vertical aliases only. Normal-C and special outer margin connectors are separate obligations.'}
 (P/'marker_neighbors_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'horizontal_checks':len(neighbors),'vertical_checks':len(vertical),'W_only_histories':len(wonly),'extended_marker_histories':len(extended),'extra_padding_required':False}))
if __name__=='__main__':main()
