#!/usr/bin/env python3
"""Independent finite CFG splice check; imports no builder/compiler/runtime.

Exact boundary checks bind the mathematical no-push and cache-test loop
proofs to every instruction of the two new sources.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def read(p):return json.loads(p.read_text())
def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else[]
def project(row,f):
    k=2 if row[0]in('inc','dec')else 1
    return row[:k]+[f(x)for x in row[k:]]
def normalized(block,base):return[project(row,lambda x:x-base)for row in block]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'verification/source_splices.json')
    a=ap.parse_args();old=read(ROOT/'construction/inputs/pa194.instructions.json')
    h=read(ROOT/'machines/PA194H/instructions.json')
    hs=read(ROOT/'machines/PA194HS/instructions.json')
    assert len(old)==3673 and len(h)==3653 and len(hs)==3650
    lo,hi=3634,3653
    incoming=[[i,t]for i,row in enumerate(old)if not lo<=i<hi for t in targets(row)if lo<=t<hi]
    assert incoming==[[3628,3634]]
    def f(i):
        assert not lo<i<hi
        return i if i<=lo else i-(hi-lo)
    n=[project(row,f)for i,row in enumerate(old)if not lo<=i<hi]
    assert len(n)==3654
    tail=[['dec',4,4,1],['inc',1,2],['inc',6,3],['jump',0],
          ['dec',6,7,5],['inc',4,6],['jump',4]]
    assert normalized(n[3634:3641],3634)==tail
    assert n[3641]==['jump',25]
    # Delete exactly the X increment while clearing the discarded old top.
    assert n[3642:3645]==[['dec',1,3645,3643],['inc',6,3644],['jump',3642]]
    assert [[i,t]for i,row in enumerate(n)if i!=3643 for t in targets(row)if t==3643]==[[3642,3643]]
    remove=3643
    def g(i):return i if i<=remove else i-1
    expected_h=[project(row,g)for i,row in enumerate(n)if i!=remove]
    assert h==expected_h
    assert h[3642:]==[
      ['dec',1,3644,3643],['jump',3642],
      ['dec',5,3648,3645],['inc',1,3646],['inc',6,3647],['jump',3644],
      ['dec',6,3651,3649],['inc',5,3650],['jump',3648],['inc',6,3652],['jump',0]]
    # The symmetric source removes restore(X,H); it sets H=1 instead.
    enters=[[i,t]for i,row in enumerate(h[:3648])for t in targets(row)if t>=3648]
    assert enters==[[3644,3648]]
    assert hs[:3648]==h[:3648]
    assert hs[3648:]==[['inc',5,3649],['jump',0]]
    # Exact guard, retained decoder and fetch interfaces for the loop proofs.
    assert hs[:11]==[
      ['dec',5,4,1],['dec',6,3,2],['jump',0],['jump',5],
      ['dec',6,10,5],['dec',5,7,6],['jump',5],['dec',6,9,8],
      ['jump',5],['jump',11],['halt']]
    assert h[:3634]==hs[:3634]==n[:3634]
    receipt={'status':'PASS','original_sites':len(old),'no_push_sites':len(n),
      'H_sites':len(h),'HS_sites':len(hs),'MP_removed_interval':[lo,hi],
      'MP_external_entries':incoming,'MP_retained_copy_restore':tail,
      'H_deleted_scratch_increment':3643,'HS_replaced_tail_start':3648,
      'HS_external_entries_to_replaced_tail':enters,
      'complete_instruction_maps_bound':True,'unchanged_prefix_sites':3634,
      'whole_program_loop_claims':'proved in proof_hybrid.tex, not inferred from sampling',
      'inputs_sha256':{str(p.relative_to(ROOT)):sha(p)for p in[
        ROOT/'construction/inputs/pa194.instructions.json',
        ROOT/'machines/PA194H/instructions.json',ROOT/'machines/PA194HS/instructions.json']}}
    a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
