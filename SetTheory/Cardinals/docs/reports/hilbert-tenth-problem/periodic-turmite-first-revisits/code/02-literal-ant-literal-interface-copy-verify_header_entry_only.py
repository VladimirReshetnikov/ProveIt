#!/usr/bin/env python3
"""Reachable normal-header INIT0 entry with no preceding old marker COPY."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,json,pathlib
from verify_copy_family import board,trace,CAT
P=pathlib.Path(__file__).resolve().parent;raw=(P/'marker_left_start.json').read_bytes();m=json.loads(raw);base=board(m['board']);copyraw=(P/'normalized_copy.json').read_bytes();cb={(x,y+600):c for x,y,c in json.loads(copyraw)['board']};box={(x+100,y+650):c for x,y,c in CAT['box']['cell_map']};assert set(base)&set(cb)==set(box)and all(base[p]==cb[p]for p in box)
old={(x+100,y+250)for x,y,c in CAT['box']['cell_map']};cases=[]
for kind in['INIT0','INIT1','WRITE0']:
 for continuation in['stop','output_READ1','next_COPY_then_READ1']:
  b=(base|cb)if continuation=='next_COPY_then_READ1'else base.copy();cnt=collections.Counter();trs=[];exits=[]
  if kind=='INIT1':b[104,254]=b[105,254]=0
  if kind=='WRITE0':end,tr=trace(b,[102,250,2],cnt);assert end==[107,249,0];trs.append(tr);exits.append(end)
  before={p:b[p]for p in old};end,tr=trace(b,[0,475,1],cnt);assert end==[600,475,1];assert not any(tuple(row[:2])in old for row in tr);trs.append(tr);exits.append(end);assert b[104,654]==b[105,654]==0;assert before=={p:b[p]for p in old}
  assert any(row[:3]==[50,475,1]for row in tr),'header FIRST absent'
  if continuation=='output_READ1':end,tr=trace(b,[103,659,0],cnt);assert end==[109,656,1];trs.append(tr);exits.append(end)
  if continuation=='next_COPY_then_READ1':
   end,tr=trace(b,[600,705,3],cnt);assert end==[0,705,3];trs.append(tr);exits.append(end);assert b[104,854]==b[105,854]==0
   end,tr=trace(b,[103,859,0],cnt);assert end==[109,856,1];trs.append(tr);exits.append(end)
  assert max(cnt.values())<=2;cases.append({'old_unused_source_kind':kind,'continuation':continuation,'phase_steps':list(map(len,trs)),'first_undefined_exits':exits,'phase_traces':trs,'max_aggregate':max(cnt.values()),'unused_old_source_preserved':True,'current_header_input_INIT0':True,'header_output':1})
out={'status':'PASS_NORMAL_HEADER_ZERO_WITHOUT_PRIOR_COPY','marker_sha256':hashlib.sha256(raw).hexdigest(),'following_COPY_sha256':hashlib.sha256(copyraw).hexdigest(),'verifier_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'cases':cases,'scope':'Normal header E-only on untouched current header input0. No old COPY activation is required; old source250 is never read. Bare normal header input1 is not claimed or required.'}
(P/'header_entry_only_receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'histories':len(cases),'steps':[c['phase_steps']for c in cases]}))
