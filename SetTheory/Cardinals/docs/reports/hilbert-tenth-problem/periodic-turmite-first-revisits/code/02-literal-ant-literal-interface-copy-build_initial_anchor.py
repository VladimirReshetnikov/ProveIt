#!/usr/bin/env python3
"""Exact constant initialization patch from the verified left-start COPY1 prefix."""
if not __debug__:raise RuntimeError('Run without -O')
import collections,hashlib,json,pathlib
P=pathlib.Path(__file__).resolve().parent;raw=(P/'marker_left_start.json').read_bytes();o=json.loads(raw);base={(x,y):c for x,y,c in o['board']}
c=next(c for c in o['cases']if c['input_kind']=='INIT1'and not c['later_output_read']);full=c['phase_traces'][0];endpoint=[50,475,1];i=next(i for i,row in enumerate(full)if row[:3]==endpoint);prefix=full[:i];suffix=full[i:];b=base.copy();setup=[[104,254,0],[105,254,0]]
for x,y,v in setup:b[x,y]=v
cnt=collections.Counter()
for x,y,h,v,xx,yy,hh in prefix:assert b[x,y]==v;b[x,y]=1-v;cnt[x,y]+=1
assert cnt[50,475]==0 and max(cnt.values())<=2
out={'status':'PASS_CONSTANT_LEFT_START_PREFIX_ANCHOR','source_json_sha256':hashlib.sha256(raw).hexdigest(),'builder_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'virtual_prefix_source_setup':setup,'virtual_prefix_entry':[600,305,3],'actual_start_state':endpoint,'endpoint_has_not_been_processed':True,'virtual_prefix_steps':len(prefix),'virtual_prefix_trace':prefix,'prefix_max_aggregate_departures':max(cnt.values()),'post_prefix_board':[[x,y,v]for(x,y),v in sorted(b.items())],'changed_cells_basis':'marker_left_start_common_INIT0_board_including_INIT1_setup','changed_cells':[[x,y,v]for(x,y),v in sorted(b.items())if base[x,y]!=v],'changed_cell_count':sum(base[p]!=v for p,v in b.items()),'verified_suffix_trace':suffix,'verified_suffix_exit':[600,475,1],'verified_suffix_logical_output':0,'scope':'Constant finite initialization changes followed by an actual trajectory that is a suffix of one verified joint COPY1-to-header-NOT history. The skipped prefix is not claimed to have physically run.'}
(P/'left_start_anchor.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'start':endpoint,'prefix_steps':len(prefix),'suffix_steps':len(suffix),'changed_cells':out['changed_cell_count'],'prefix_max':max(cnt.values())}))
