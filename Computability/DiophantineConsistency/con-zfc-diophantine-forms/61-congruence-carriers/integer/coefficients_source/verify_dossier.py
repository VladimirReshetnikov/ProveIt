#!/usr/bin/env python3
"""Authenticate this dossier and the complete regenerated coefficient tuple."""
import gzip, hashlib, json, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def require(c,m):
    if not c:raise RuntimeError(m)

def main():
    ledger=json.loads((ROOT/'TRANSFER_LEDGER.json').read_text())
    for item in ledger['files']:
        b=(ROOT/item['local']).read_bytes()
        require(len(b)==item['verified_bytes'],'Source size '+item['local'])
        require(hashlib.sha256(b).hexdigest()==item['sha256'],'Source SHA256 '+item['local'])
        require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==item['git_blob_sha1'],'Source Git blob '+item['local'])
    old=json.loads((ROOT/'coefficients/payloads/COEFFICIENT_BINDING.json').read_text())
    new=json.loads((ROOT/'generated_payloads/COEFFICIENT_BINDING.json').read_text())
    require(old==new,'Whole coefficient manifest differs')
    for name,m in old['payloads'].items():
        raw=(ROOT/'generated_payloads'/(name+'.bin')).read_bytes()
        gz=(ROOT/'generated_payloads'/(name+'.bin.gz')).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==m['sha256'],'Raw coefficient '+name)
        require(hashlib.sha256(gz).hexdigest()==m['gzip_sha256'],'Gzip coefficient '+name)
        require(gzip.decompress(gz)==raw,'Decompression '+name)
        require(int.from_bytes(raw,'little').bit_length()==m['bits'],'Bit length '+name)
    binding=json.loads((ROOT/'ACTIVE_BINDING.json').read_text())
    require(binding['variant']==old['variant'],'Active coefficient variant')
    require(binding['B']==old['B'],'Active radix')
    require(hashlib.sha256((ROOT/binding['whole_manifest']).read_bytes()).hexdigest()==binding['whole_manifest_sha256'],'Active manifest hash')
    for alias,name in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        entry=binding['ports'][alias]
        require(all(entry[k]==v for k,v in old['payloads'][name].items()),'Active port metadata '+alias)
        require(hashlib.sha256((ROOT/entry['payload']).read_bytes()).hexdigest()==entry['sha256'],'Active port '+alias)
        require(hashlib.sha256((ROOT/entry['gzip_payload']).read_bytes()).hexdigest()==entry['gzip_sha256'],'Active compressed port '+alias)
    for entry in binding['polynomials']+[binding['source_quartic']]:
        require(hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest()==entry['sha256'],'Active polynomial hash '+entry['path'])
        packet=json.loads((ROOT/entry['path']).read_text())
        require(packet['fixed_numerals']==list(binding['ports']),'Active polynomial port order')
    # Reuse the newly authored exact polynomial utility on independently read
    # historical packets; no historical Python program is imported/executed.
    sys.path.insert(0,str(ROOT.parent))
    import eliminate as e
    historical=[]
    for count,degree,lead in [(42,6,{'Jrep':2,'L':2,'v_scale':2,'Bm1':2}),
                              (36,8,{'Jrep':6,'v_scale':2,'Bm1':6})]:
        fn=f'integer{count}_degree{degree}_odd_scale.json'
        p=json.loads((ROOT/'historical'/fn).read_text())
        e.VARS=p['variables'];e.PORTS=p['fixed_numerals'];e.NAMES=e.VARS+e.PORTS
        e.IDX={v:i for i,v in enumerate(e.NAMES)};e.ZERO=(0,)*len(e.NAMES)
        ps=[e.parse(s) for s in p['residuals']]
        require(len(e.VARS)==p['variable_count']==count,'Historical variables')
        require(len(ps)==p['equation_count'],'Historical residual count')
        require(list(map(e.degree,ps))==p['residual_degrees'],'Historical residual degrees')
        poly={}
        for r in ps:poly=e.add(poly,e.mul(r,r))
        require(e.degree(poly)==degree,'Historical polynomial degree')
        exponent=tuple(lead.get(v,0) for v in e.NAMES)
        require(poly.get(exponent)==4,'Historical nonzero leading coefficient')
        require(len(poly)==p['expanded_symbolic_terms'],'Historical symbolic terms')
        historical.append({'file':fn,'variables':count,'residuals':len(ps),'degree':degree,
                           'symbolic_sos_terms':len(poly),'leading_monomial':lead,'leading_coefficient':4})
    result={'status':'PASS','source_git_blobs_checked':len(ledger['files']),
            'whole_manifest_identical':True,'raw_and_gzip_payloads_identical':True,
            'active_polynomial_and_port_bindings_checked':True,
            'historical_comparisons':historical}
    (ROOT/'DOSSIER_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
