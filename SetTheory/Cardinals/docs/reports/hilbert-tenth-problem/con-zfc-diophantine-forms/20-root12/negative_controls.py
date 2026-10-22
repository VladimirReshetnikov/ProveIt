#!/usr/bin/env python3
"""Check that the shipped-data preflight rejects three controlled corruptions."""
import json
from pathlib import Path
import shutil
import sys
import tempfile
sys.dont_write_bytecode = True
import verify
ROOT=Path(__file__).resolve().parent

def main():
    checks=[]
    with tempfile.TemporaryDirectory(prefix='con_zfc_negative_') as td:
        root=Path(td)
        for folder in ['amalgamation','arithmetic','domains','coefficients']:
            shutil.copytree(ROOT/folder,root/folder,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        shutil.copy2(ROOT/'INSTANCE.json',root/'INSTANCE.json')
        verify.coefficients(root);verify.transitions(root);verify.packets(root)
        cases=[
            ('coefficient_byte_corruption','coefficients/expanded/beta.bin',verify.coefficients),
            ('shifted_mask_alias_corruption','amalgamation/main_root12_product.json',verify.packets),
            ('literal_transition_table_corruption','coefficients/sources/k215.tm',verify.transitions)]
        for name,rel,checker in cases:
            path=root/rel;original=path.read_bytes()
            if name=='shifted_mask_alias_corruption':
                p=json.loads(original);p['coefficient_binding']['aliases']['MF']='MF_native'
                path.write_text(json.dumps(p))
            else:
                changed=bytearray(original);changed[-1]^=1;path.write_bytes(changed)
            try:
                checker(root)
            except ValueError as exc:
                checks.append({'control':name,'rejected':True,'reason':str(exc)})
            else:
                raise RuntimeError('Corruption was not rejected: '+name)
            finally:
                path.write_bytes(original)
        verify.coefficients(root);verify.transitions(root);verify.packets(root)
    result={'status':'PASS','original_data_passed_before_and_after':True,'controls':checks,
            'scope':'Integrity and coherent-binding controls, not semantic counterexamples or a proof of the Diophantine equivalence.'}
    (ROOT/'NEGATIVE_CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
