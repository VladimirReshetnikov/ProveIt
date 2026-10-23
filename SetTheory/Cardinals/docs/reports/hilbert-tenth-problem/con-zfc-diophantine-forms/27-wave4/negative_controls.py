#!/usr/bin/env python3
"""Deliberate integrity and instance-binding failures, in disposable copies."""
from pathlib import Path
import json
import shutil
import tempfile
import verify

ROOT=Path(__file__).resolve().parent

def rejected(action):
    try:action()
    except (ValueError,FileNotFoundError,KeyError):return True
    return False

def main():
    if not __debug__:raise ValueError('Do not run with -O')
    controls=[]
    with tempfile.TemporaryDirectory(prefix='con_zfc_corrupt_') as td:
        root=Path(td)/'release';shutil.copytree(ROOT,root)
        p=root/'coefficients/expanded/MC.bin';old=p.read_bytes()
        p.write_bytes(bytes([old[0]^1])+old[1:])
        verify.require(rejected(lambda:verify.check_manifest(root)),'Corrupt coefficient escaped seal')
        verify.require(rejected(lambda:verify.check_instance(root)),'Corrupt coefficient escaped tuple check')
        controls.append('One-bit MC corruption rejected by both seal and tuple binding')
        p.write_bytes(old)
        p=root/'norms/two_weight_norm12_product.json';old=p.read_bytes();obj=json.loads(old)
        obj['coefficient_binding']['tuple_id']='a-different-compiler'
        p.write_text(json.dumps(obj))
        verify.require(rejected(lambda:verify.check_instance(root)),'Stale packet escaped binding check')
        controls.append('Spliced packet coefficient binding rejected')
        p.write_bytes(old)
        p=root/'nine/source/nine/generated/constants.json';old=p.read_bytes();p.unlink()
        verify.require(rejected(lambda:verify.check_manifest(root)),'Missing dependency escaped seal')
        controls.append('Missing fixed-index dependency rejected')
        p.write_bytes(old)
        verify.check_manifest(root);verify.check_instance(root)
    receipt={'status':'PASS','controls':controls,'restored_copy_valid':True,
             'scope':'Integrity and binding failures, not mathematical countermodel search.'}
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
