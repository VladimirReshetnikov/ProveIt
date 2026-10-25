"""Reconstruct the new circuit and all fixed coefficient payloads offline."""
from pathlib import Path
from copy import deepcopy
import gzip
import hashlib
import json
from construct_coefficients import construct, raw_bytes

ROOT=Path(__file__).resolve().parent
def build(variant='lower'):
    parent=json.loads((ROOT/'upstream133/compact/equation_85.json').read_text())
    result=deepcopy(parent)
    rows=[]
    for row in parent['source']:
        if row[0]=='L':
            if variant=='sharp':
                rows.extend([['d0','*','Am1','UE'],['d','+','d0','UE']])
            else:rows.append(['d','*','Am1','UE'])
            rows.extend([['bB','*','cTR','Bt'],
                         ['dmbB','-','d','bB'],['Vcenter','*','V','dmbB']])
        elif row[0]=='LBt':continue
        elif row[0]=='center':rows.append(['center','+','n','Vcenter'])
        else:rows.append(row)
    degree=318 if variant=='sharp' else 323
    result.update(name=variant+'_centered_doubled_product_square',source=rows,
        operations=len(rows),operation_breakdown={o:sum(r[1]==o for r in rows) for o in ('*','+','-')},
        exact_degree=degree,transport_weight='bV; factored carrier n+V*(d-bB)',
        proof='PROOF.md',proof_status='Ordinary lower-center shear of pinned package133; constructive positive completeness; inherited native/refutation calibration.',
        parent_commit='1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61',
        parent_path='Computability/DiophantineConsistency/con-zfc-diophantine-forms/133-staged-certificates/compact/equation_85.json')
    result.pop('parent_sha256',None)
    (ROOT/'coefficients').mkdir(exist_ok=True)
    for name,value in construct().items():
        raw=raw_bytes(value)
        port=result['coefficient_binding']['ports'][name]
        if hashlib.sha256(raw).hexdigest()!=port['raw_sha256'] or value.bit_length()!=port['bits']:
            raise ValueError('fixed coefficient does not match pinned whole tuple')
        payload=gzip.compress(raw,compresslevel=9,mtime=0)
        (ROOT/'coefficients'/port['file']).write_bytes(payload)
        port['gzip_sha256']=hashlib.sha256(payload).hexdigest()
    (ROOT/f'equation_{len(rows)}_degree{degree}.json').write_text(json.dumps(result,indent=2)+'\n')
    return {'operations':len(rows),'exact_degree':degree,'coefficient_payloads':4}
if __name__=='__main__':print(json.dumps([build('lower'),build('sharp')],indent=2))
