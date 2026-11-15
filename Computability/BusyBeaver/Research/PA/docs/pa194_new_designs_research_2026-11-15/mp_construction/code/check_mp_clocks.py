#!/usr/bin/env python3
"""Finite coefficient audit for the explicit iPRA time-transfer bound."""
from pathlib import Path
import argparse,hashlib,json
PARENT_SHA='392222868a523b10d759138d17420193a057ce8a240730069666f22286c2de2f'
def analyze(name,data,startup):
    contracts=json.loads(data);assert len(contracts)==4778
    vv=[x['duration']for x in contracts]
    assert all(len(c)==13 and all(isinstance(n,int)and n>=0 for n in c)for c in vv)
    assert min(c[0]for c in vv)==3
    maxima=[max(c[i]for c in vv)for i in range(13)]
    assert maxima==[534,8,4,4,4,4,4,4,2,4,4,2,2]
    intercept=max(c[0]+2*max(c[2:11])+c[11]+75*c[12]for c in vv)
    slope=max(c[1]+max(c[2:11])+3*c[12]for c in vv)
    assert(intercept,slope)==(694,18)
    return{'name':name,'contracts':4778,'contracts_sha256':hashlib.sha256(data).hexdigest(),'minimum_duration_constant':3,'componentwise_maximum':maxima,'step_intercept':intercept,'step_slope':slope,'startup':startup,'cumulative_bound':{'constant':startup,'linear':685,'quadratic':9},'posthalt_duration':1}
def main():
    assert __debug__
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--parent-contracts',type=Path,required=True);p.add_argument('--child-contracts',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    data=a.parent_contracts.read_bytes();assert hashlib.sha256(data).hexdigest()==PARENT_SHA
    parent=analyze('exact revised AX11H',data,57922);child=analyze('MP reassociation',a.child_contracts.read_bytes(),58066)
    assert child['contracts_sha256']=='bf7b312a0f5ad38319df388ef063399e74c4a09bdcc1c7bb73b2725a4950cca4'
    result={'status':'PASS','parent':parent,'child':child,'common_bound':{'constant':58066,'linear':685,'quadratic':9},'parent_archive_sha256':'93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075','proof_scope':'Finite affine coefficient comparison. Source bookkeeping, address closure, exact runtime and uniform mathematical rule soundness are separate premises in relative_proof.tex.'}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
