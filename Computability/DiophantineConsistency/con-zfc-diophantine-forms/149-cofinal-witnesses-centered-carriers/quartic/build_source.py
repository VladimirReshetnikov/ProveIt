#!/usr/bin/env python3
"""Frozen ordinary-proof-backed odd-square source edit; no search or network."""
import argparse,copy,hashlib,json
from pathlib import Path

def emit(o):return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def construct(root):
 cert=json.loads((root/'sources/odd_square_composition_certificate.json').read_text())
 raw=(root/'sources'/cert['source']).read_bytes()
 if hashlib.sha256(raw).hexdigest()!=cert['source_sha256']:raise ValueError('source hash')
 old=json.loads(raw);out=copy.deepcopy(old);i=cert['replaced_row']
 if old['residuals'][i]!=cert['old_row']:raise ValueError('source row')
 out['residuals'][i]=cert['new_row_before_compaction']
 out['variables'].append({'name':'radix.odd_square_root','kind':'signed_witness'})
 keep=cert['retained_extended_coordinates'];rename={v:i for i,v in enumerate(keep)}
 out['variables']=[out['variables'][i] for i in keep]
 for r in out['residuals']:r['terms']=[[c,[rename[v] for v in m]] for c,m in r['terms']]
 out['variant']+=':odd_square_radix'
 if hashlib.sha256(emit(out)).hexdigest()!=cert['output_sha256']:raise ValueError('output hash')
 return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--release',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);p.add_argument('--check',action='store_true');a=p.parse_args();raw=emit(construct(a.release));path=a.output or a.release/'sources/common_remainders250_odd.json'
 if a.check:
  if path.read_bytes()!=raw:raise ValueError('source replay differs')
 else:path.write_bytes(raw)
 print(json.dumps({'status':'pass','variables':250,'rows':182,'check_only':a.check}))
