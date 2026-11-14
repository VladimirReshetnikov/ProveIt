#!/usr/bin/env python3
"""Independent structural certificate for the QH→QHS source replacement.
The universal mathematical lemma is stated in qhs_source_proof.txt. This
checker binds its exact loop patterns and incoming-edge condition to the
complete supplied source arrays; it imports no compiler or simulator.
"""
from pathlib import Path
import argparse,json,hashlib

def edges(row):
 op=row[0]
 if op=='inc':return [(row[2],'next')]
 if op=='dec':return [(row[2],'zero'),(row[3],'positive')]
 if op=='jump':return [(row[1],'jump')]
 if op=='halt':return []
 raise ValueError(op)

def main():
 a=argparse.ArgumentParser();a.add_argument('old',type=Path);a.add_argument('new',type=Path);a.add_argument('--output',type=Path);a=a.parse_args()
 oldb=a.old.read_bytes();newb=a.new.read_bytes();old=json.loads(oldb);new=json.loads(newb)
 assert len(old)==3653 and len(new)==3650
 assert old[:3648]==new[:3648]
 assert old[3642:3648]==[['dec',1,3644,3643],['jump',3642],['dec',5,3648,3645],['inc',1,3646],['inc',6,3647],['jump',3644]]
 assert old[3648:]==[['dec',6,3651,3649],['inc',5,3650],['jump',3648],['inc',6,3652],['jump',0]]
 assert new[3648:]==[['inc',5,3649],['jump',0]]
 comparator=[['dec',5,4,1],['dec',6,3,2],['jump',0],['jump',5],['dec',6,10,5],['dec',5,7,6],['jump',5],['dec',6,9,8],['jump',5],['jump',11],['halt']]
 assert old[:11]==new[:11]==comparator
 incoming=[(i,j,branch) for i,row in enumerate(old[:3648]) for j,branch in edges(row) if j>=3648]
 assert incoming==[(3644,3648,'zero')]
 assert all(0<=j<len(old) for row in old for j,_ in edges(row))
 assert all(0<=j<len(new) for row in new for j,_ in edges(row))
 r={'status':'PASS','old_source_sha256':hashlib.sha256(oldb).hexdigest(),'new_source_sha256':hashlib.sha256(newb).hexdigest(),'old_sites':len(old),'new_sites':len(new),'identical_prefix_sites':3648,'only_external_tail_edge':incoming,'established_boundary':'Register5 H=0 at source3648; register6 X=k arbitrary; every other register unchanged by tail/comparator except their common behavior.','common_comparator':'halts iff H=X; otherwise reaches11 with H=X=0, preserving all other registers','old_tail':'(H,X)=(0,k) -> (k,1)','new_tail':'(H,X)=(0,k) -> (1,k)','source_steps_saved_by_new_tail_and_comparator':{'k=0':0,'k=1':4,'k>=2':'2*k+4'},'kernel_checked':False,'proof_boundary':'Exact structural binding to universal PA-formalizable loop lemma; no sampling used as universal evidence.'}
 if a.output:a.output.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
if __name__=='__main__':main()
