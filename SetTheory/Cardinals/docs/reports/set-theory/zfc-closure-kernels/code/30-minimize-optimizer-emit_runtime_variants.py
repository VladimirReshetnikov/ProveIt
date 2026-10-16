#!/usr/bin/env python3
"""Emit literal prepared-tape cores. No blank-tape consistency claim."""
from pathlib import Path
import json,hashlib
from analyze_table import parse_table
ROOT=Path(__file__).parent

def rows():
 table,*_=parse_table(ROOT/'sources/zfc_254.tm')
 table[3,0]=(0,'L',48)
 out={k:v for k,v in table.items() if k[0] not in (5,8)}
 assert len(out)==504
 assert {v[2] for v in out.values()}-set(q for q,b in out)=={254}
 return out

def main():
 folder=ROOT/'machines';folder.mkdir(exist_ok=True)
 base=rows();reports=[]
 for name,target in [('runtime252',64),('runtime252-detour54',54),('runtime252-detour66',66),('runtime252-detour114',114)]:
  table=base.copy()
  if target!=64:table[49,1]=(1,'L',target)
  text='# Prepared-tape runtime core only; no blank-tape consistency claim.\n#! start 96\n'+''.join(f'{q} {b} {w} {d} {r}\n' for(q,b),(w,d,r) in sorted(table.items()))
  p=folder/(name+'.tm');p.write_text(text)
  reports.append({'file':str(p.relative_to(ROOT)),'states':252,'transitions':504,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'entry_state':96,'table_start_is_for_prepared_seed':True,'delta_49_read1':list(table[49,1])})
 ones=[-1,40];pos=41
 for value in [0,0,0,0,0,0,2,0,0]:
  pos+=1
  for j in range(value+1):ones.append(pos);pos+=1
 seed={'state':96,'head':0,'ones':ones,'all_other_cells':0,'physical_primary':[0,0,0,0,0,0,2,0,0],'gap':40,'spare_blocks':[],'scope':'Externally supplied finite seed; it is not the blank tape.'}
 (folder/'prepared_seed.json').write_text(json.dumps(seed,indent=2)+'\n')
 (ROOT/'runtime_variant_manifest.json').write_text(json.dumps(reports,indent=2)+'\n')
 print('Emitted four prepared-tape runtime tables and explicit finite seed.')
if __name__=='__main__':main()
