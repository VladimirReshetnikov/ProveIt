#!/usr/bin/env python3
"""Independent finite audit of the 19-instruction no-push splice."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).parent
a=json.loads((ROOT/'inputs/original_tag196.instructions.json').read_text())
b=json.loads((ROOT/'machine/instructions.json').read_text())
lo,hi=3646,3665
assert len(a)==3685 and len(b)==3666
removed=set(range(lo,hi))
def targets(row):return row[2:]if row[0]in('inc','dec')else row[1:]if row[0]=='jump'else[]
def relocate(x):return x if x<lo else lo if x in removed else x-(hi-lo)
def rowmap(row):
 if row[0]in('inc','dec'):return row[:2]+[relocate(x)for x in row[2:]]
 if row[0]=='jump':return ['jump',relocate(row[1])]
 return row
incoming=[]
for i,row in enumerate(a):
 if i in removed:continue
 assert rowmap(row)==b[relocate(i)],(i,row,b[relocate(i)])
 for target in targets(row):
  if target in removed:incoming.append((i,target))
assert incoming==[(3640,3646)]
def rows(p):return {tuple(map(int,ln.split()[:2])):ln.split()[2:]for ln in p.read_text().splitlines()}
aT=rows(ROOT/'inputs/original_tag196.native.tm');bT=rows(ROOT/'machine/machine.native.tm')
assert aT.keys()==bT.keys()
diff=[{'row':list(k),'old':aT[k],'new':bT[k]}for k in aT if aT[k]!=bT[k]]
assert diff==[{'row':[164,1],'old':['1','R','98'],'new':['1','R','114']}],diff
receipt={'passed':True,'old_source_sites':len(a),'new_source_sites':len(b),'deleted_halfopen_interval':[lo,hi],
 'deleted_primitive_count':19,'unique_external_entry':incoming[0],
 'every_retained_instruction_and_successor_preserved':True,'literal_differences':diff,
 'native_sha256':hashlib.sha256((ROOT/'machine/machine.native.tm').read_bytes()).hexdigest(),
 'dense_sha256':hashlib.sha256((ROOT/'machine/machine.tm').read_bytes()).hexdigest()}
(ROOT/'source_splice_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
