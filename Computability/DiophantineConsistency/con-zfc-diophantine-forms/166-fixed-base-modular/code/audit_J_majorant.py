#!/usr/bin/env python3
"""A finite structural certificate for |J| <= H^(2^22) for signed inputs.

If H>=2 and |a_i-1|<=H, a source gate g=sum c_m prod v_i has
|g|<=H^(ceil(log2 sum |c_m|)+max_m sum e(v_i)).  This audit extracts the
actual 91-gate ancestor graph of J, without expanding its enormous polynomial.
"""
from pathlib import Path
from functools import lru_cache
import argparse, hashlib, json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def certificate(source):
    data=json.loads(source.read_text()); defs={}
    for ri,row in enumerate(data['residuals']):
        for c,m in row['terms']:
            if len(m)!=1 or c not in (-1,1):continue
            i=m[0]
            if data['variables'][i]['kind']!='gate':continue
            if all(all(j<i for j in mm) for cc,mm in row['terms'] if mm!=[i]):
                rhs=[[-cc*c,mm] for cc,mm in row['terms'] if mm!=[i]]
                if i not in defs:defs[i]=(ri,rhs)
    ledger=[]
    @lru_cache(None)
    def exponent(i):
        if 16<=i<=24:return 1
        if i not in defs:raise ValueError(('unaccounted leaf',i))
        ri,rhs=defs[i]; l1=sum(abs(c) for c,m in rhs)
        ce=(l1-1).bit_length(); me=max(sum(exponent(j) for j in m) for c,m in rhs)
        value=ce+me
        ledger.append({'id':i,'name':data['variables'][i]['name'],'source_row':ri,'rhs_terms':rhs,
          'coefficient_l1':l1,'coefficient_exponent':ce,'monomial_exponent':me,'exponent':value})
        return value
    target=next(i for i,v in enumerate(data['variables']) if v['name']=='add.380')
    e=exponent(target)+1
    if not e < 2**22:raise ValueError(('exponent budget exceeded',e))
    leaves=sorted({j for r in ledger for c,m in r['rhs_terms'] for j in m if j not in defs})
    if leaves!=[16,17,18,19]:raise ValueError(('unexpected leaves',leaves))
    return {'schema':'signed_J_structural_majorant_v1','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'seed_ids':leaves,'seed_exponent':1,'gate_ledger':ledger,'gate_count':len(ledger),'target_wire':target,
      'target_expression':[[1,[]],[1,[target]]],'computed_exponent':e,'adopted_exponent':2**22,
      'hypotheses':'H>=2 and |wire_i|<=H for seed i. Here wire_i=a_i-1 and H>=2+a_i^2 suffices for every integer a_i.',
      'conclusion':'|J|<=H^3649857<=H^(2^22), for arbitrary signed representatives.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=ROOT/'stages/modular/raw_source.json');ap.add_argument('--output',type=Path)
    ap.add_argument('--check',action='store_true')
    ap.add_argument('--certificate',type=Path,default=ROOT/'stages/modular/J_majorant_certificate.json')
    a=ap.parse_args();c=certificate(a.source)
    if a.check and json.loads(a.certificate.read_text())!=c:
        raise ValueError('Stored signed-J ledger differs from the independent reconstruction')
    if a.output:a.output.write_text(json.dumps(c,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps({k:c[k] for k in ('source_sha256','gate_count','seed_ids','computed_exponent','adopted_exponent','conclusion')},indent=2))
