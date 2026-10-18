#!/usr/bin/env python3
"""Transfer finite register fixtures after checking every ordered source leaf."""
import argparse,hashlib,json
from pathlib import Path
from safe_lifetime_witness import parse_table
P=argparse.ArgumentParser();P.add_argument('--program',type=Path,required=True);P.add_argument('--sites',type=Path,required=True);P.add_argument('--metadata',type=Path,required=True);P.add_argument('--output',type=Path,required=True);a=P.parse_args();nodes=parse_table(a.program.read_text());old=[]
def walk(i,p):
 for b,(op,arg)in enumerate(nodes[i]):
  if op=='CN':walk(arg,p+str(b))
  else:old.append([p+str(b),op,arg])
walk(0,'');new=json.loads(a.sites.read_text());assert len(old)==len(new)==6460
assert [x[1:]for x in old]==[x[1:]for x in new]
metadata=json.loads(a.metadata.read_text());result=[]
for row in metadata:
 i=row['program_index'];assert old[i]==[row['pc'],row['instruction'],row['logical_register']]
 out=row.copy();out['old_pc']=out['pc'];out['pc']=new[i][0];result.append(out)
a.output.write_text(json.dumps(result,indent=2)+'\n')
check=dict(status='PASS_EXACT_ORDERED_LEAF_TRANSFER',source_leaves=6460,transferred_fixtures=len(result),all_instruction_labels_and_arguments_identical=True,source_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in[a.program,a.sites,a.metadata]},scope='Exact static leaf correspondence only; dynamic equivalence is checked by a separate register-machine bisimulation certificate.')
a.output.with_suffix('.transfer.json').write_text(json.dumps(check,indent=2)+'\n');print(json.dumps(check,indent=2))
