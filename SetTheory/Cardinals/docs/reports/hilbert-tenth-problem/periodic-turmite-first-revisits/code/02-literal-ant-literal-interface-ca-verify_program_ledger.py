#!/usr/bin/env python3
"""Independent closed-form count and bounds for the compressed row program."""
if not __debug__:raise RuntimeError('Assertions required')
import collections,hashlib,json,pathlib
R=pathlib.Path(__file__).resolve().parent
b=(R/'physical_program.json').read_bytes();p=json.loads(b);d=json.loads((R/'fixed_ca_cell.json').read_text())
assert p['swap_linear_constant']==14
n=24;g=len(d['nand_gates']);B=40;count=collections.Counter()
def copying(r):
 assert r>=1
 return collections.Counter(DUP=12*r-11,NAND=12*r-12,MOVE_RIGHT=6*r*r-6,MOVE_LEFT=6*r*r+3*r-9)
# Gather uniformly spaced inputs, then append every named NAND wire.
count['MOVE_LEFT']+=(B-1)*n*(n-1)//2
for j,(u,v)in enumerate(d['nand_gates']):
 width=n+j;assert 0<=u<width and 0<=v<width
 count.update(copying(width-u));count.update(copying(width+1-v));count['NAND']+=1
width=n+g
for v in d['complemented_phi_outputs']+[d['halt_wire']]:
 assert 0<=v<n+g;count.update(copying(width-v));width+=1
observe=sum(count.values());col=width-1
count['DUP']+=1
count['MOVE_LEFT']+=n*(n+g)
count['MOVE_RIGHT']+=(B-1)*n*(n-1)//2
assert observe==p['observer_row_index']and col==p['observer_column_index']
assert sum(count.values())==p['program_rows']==p['prefix_rows'][-1]
assert n*B==p['tile_slots']and p['active_columns']==n*B-2
# No hidden universal-bound assumption: prove bounds separately by syntax types.
for node in p['nodes']:
 t=node['type']
 if t=='GATE':maximum=node['m']+5
 elif t=='COPY':maximum=node['m']+4
 elif t=='RANGE':
  rr=range(node['start'],node['stop'],node['step']);maximum=max(rr)+1
 elif t=='ROW':maximum=node['i']+1
 else:raise AssertionError(t)
 assert maximum<p['active_columns'],(node,maximum)
result={'status':'PASS_EXACT_COMPRESSED_PROGRAM_LEDGER','program_sha256':hashlib.sha256(b).hexdigest(),
 'physical_pair_rows':dict(count),'total_rows':sum(count.values()),'observer_row':observe,'observer_column':col,
 'selected_slot_stride':B,'active_columns':p['active_columns'],'all_row_indices_proved_in_range_by_node_syntax':True,
 'closed_form_copy_to_end':'For r=width-source_index: DUP=12r-11,NAND=12r-12,MR=6r²-6,ML=6r²+3r-9; total12r²+27r-38',
 'closed_form_swap':'For r=word_width-left_index: DUP12,NAND12,MR12r-7,ML12r-3; total24r+14',
 'source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
 'physical_global_atlas_complete':False}
(R/'program_ledger.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['physical_pair_rows']|{'total':result['total_rows'],'status':result['status']}))
