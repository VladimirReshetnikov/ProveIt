#!/usr/bin/env python3
"""Audit partial/direct negation source rewrites using exact symbolic contracts.

This confirms only the old-to-new negation change within each supplied pair.
It does not assert that distinct base words use the same logical formulas.
"""
from pathlib import Path
import json,hashlib
from audit_negation_peephole import Pool,PATTERN,REPLACEMENT

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'source_variant_inputs.json'

def audit(old,new,label):
 assert old.endswith('YZGaZ') and new.endswith('YZGaZ')
 p=Pool();r=[p.make('variable',i) for i in range(9)];r[6]=r[7]=0
 trace=p.replay(old[:-5],r);i=j=0;offsets=[]
 while i<len(old)-5:
  if old.startswith(PATTERN,i) and new.startswith(REPLACEMENT,j):
   assert trace[i][6]==trace[i][7]==0,(label,i,'dirty scratch')
   assert p.replay(REPLACEMENT,trace[i])[-1]==trace[i+len(PATTERN)]
   offsets.append(i);i+=len(PATTERN);j+=len(REPLACEMENT)
  else:
   assert old[i]==new[j],(label,i,j,'unexpected source edit')
   i+=1;j+=1
 assert new[j:]=='YZGaZ'
 assert p.replay(new[:-5],r)[-1]==trace[-1]
 return dict(label=label,replacements=len(offsets),original_offsets=offsets,
             old_length=len(old),new_length=len(new),all_sites_clean=True,
             same_nine_register_outputs=True,
             old_sha256=hashlib.sha256(old.encode()).hexdigest(),
             new_sha256=hashlib.sha256(new.encode()).hexdigest())

def main():
 data=json.loads(SOURCE.read_text())
 results=[audit(data['bases'][v['base']],v['word'],v['label']) for v in data['variants']]
 out=dict(status='PASS_SYMBOLIC_ALL_REGISTER_OUTPUTS',input_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
          variants=len(results),reports=results,
          scope='Each supplied base-to-variant transformation consists only of proved clean negation contractions. Distinct base formulas and the literal binary compiler are separate obligations.')
 (HERE/'source_variants_audit.json').write_text(json.dumps(out,indent=2)+'\n')
 print('PASS',len(results),'partial/direct source variants;',sum(r['replacements'] for r in results),'clean contraction applications')

if __name__=='__main__':main()
