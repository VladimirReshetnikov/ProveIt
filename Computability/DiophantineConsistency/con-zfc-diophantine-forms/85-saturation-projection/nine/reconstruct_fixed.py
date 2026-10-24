#!/usr/bin/env python3
"""Reconstruct four native ports from the fixed seed, then all11 fixed leaves."""
from pathlib import Path
import gzip,hashlib,json,math,subprocess,sys
ROOT=Path(__file__).resolve().parent
def require(p,m):
    if not p:raise ValueError(m)
def main():
    # Retained, read-reviewed repository tool; exact source bytes pinned.
    subprocess.run([sys.executable,str(ROOT/'provenance/verify_one_page_tuple54.py'),
                    '--seed',str(ROOT/'coefficients/COMPACT54_SEED.txt'),
                    '--reference-dir',str(ROOT/'coefficients/compact_tuple'),
                    '--receipt',str(ROOT/'COEFFICIENT_RECONSTRUCTION.json')],check=True,
                   stdout=subprocess.DEVNULL)
    receipt_path=ROOT/'COEFFICIENT_RECONSTRUCTION.json'
    native_receipt=json.loads(receipt_path.read_text());native_receipt.pop('seconds',None)
    receipt_path.write_text(json.dumps(native_receipt,indent=2)+'\n')
    order=['beta','K','MC','MF_source']
    ports=[int.from_bytes(gzip.decompress((ROOT/'coefficients/compact_tuple'/(name+'.bin.gz')).read_bytes()),'little') for name in order]
    parent=json.loads((ROOT/'upstream/gap2082_positive.json').read_text())
    expected={r['name']:sum(t['integer']*math.prod(v**e for v,e in zip(ports,t['port_powers'])) for t in r['terms']) for r in parent['coefficient_recipes']}
    expected['base_scale']=1<<parent['base_scale_exponent']
    expected['threshold_'+str(parent['threshold_scale_exponent'])]=1<<parent['threshold_scale_exponent']
    binding=json.loads((ROOT/'fixed/BINDING.json').read_text());records=[]
    require(set(expected)=={r['name'] for r in binding['records']},'complete11-leaf recipe set')
    for r in binding['records']:
        value=expected[r['name']]
        require((value>0)-(value<0)==r['sign'],'fixed sign')
        actual=gzip.decompress((ROOT/r['path']).read_bytes())
        raw=abs(value).to_bytes(max(1,(abs(value).bit_length()+7)//8),'little')
        require(raw==actual,'complete-byte fixed reconstruction '+r['name'])
        records.append({'name':r['name'],'raw_bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'equal':True})
    result={'native_ports':'reconstructed from complete1294-digit seed by pinned finite recipe',
            'fixed_leaves':records,'scope':'Finite exact numeral identities; no native semantic calibration inferred.'}
    (ROOT/'FIXED_RECONSTRUCTION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'native_ports':4,'fixed_leaves':len(records),'status':'PASS'}))
if __name__=='__main__':main()
