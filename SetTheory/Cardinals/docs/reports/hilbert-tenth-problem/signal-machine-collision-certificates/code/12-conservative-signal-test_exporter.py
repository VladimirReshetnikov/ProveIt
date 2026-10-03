#!/usr/bin/env python3
"""Exhaustive independent polynomial expansion checks on selected small packets."""
import gzip,json,tempfile
from collections import Counter
from pathlib import Path
from compile_packet import Compiler,export_residuals,export_expanded
HERE=Path(__file__).resolve().parent
C=Compiler().close();allbranches=C.branches
sets=[[0],[0,79695,next(i for i,b in enumerate(allbranches) if len(b[2])==2)], [0,10,100,1000,10000]]
receipts=[]
for branchids in sets:
 C.branches=[allbranches[i] for i in branchids];C.B=len(C.branches);C.copy_base=36+C.B;C.slack_base=36+19*C.B;C.offsets=[];C.T=0
 if hasattr(C,'rowstarts'):del C.rowstarts
 for s,t,J in C.branches:C.offsets.append(C.T);C.T+=sum(c>=0 for c in C.cs[s])+19-len(J)
 C.V=C.slack_base+C.T
 with tempfile.TemporaryDirectory() as td:
  residual=Path(td)/'r.gz';expanded=Path(td)/'e.gz'
  rows=export_residuals(C,residual);count=export_expanded(C,expanded)
  expected=Counter()
  with gzip.open(residual,'rt') as f:
   for line in f:
    row=json.loads(line);terms=[(i,int(v)) for i,v in row['terms']]
    if int(row['constant']):terms.append((-1,int(row['constant'])))
    for a,(i,x) in enumerate(terms):
     for j,y in terms[a:]:expected[min(i,j),max(i,j)]+=x*y*(1 if i==j else 2)
  for r in range(C.B):
   for s in range(C.B):
    if r!=s:
     for i in range(18):expected[C.selector(r),C.copy(s,i)]+=1
  expected={k:v for k,v in expected.items() if v}
  found={}
  with gzip.open(expanded,'rt') as f:
   for line in f:
    i,j,v=json.loads(line);assert (i,j) not in found;found[i,j]=int(v)
  assert found==expected and len(found)==count
  for i in range(-1,C.V):
   for j in range(i,C.V):
    got=C.coefficient(j) if i==-1 and j!=-1 else C.coefficient(-1) if i==j==-1 else C.coefficient(i,j)
    assert got==expected.get((i,j),0),(i,j,got,expected.get((i,j),0))
  receipts.append(dict(branch_ids=branchids,variables=C.V,rows=rows,expanded_terms=count,all_coefficient_queries_match=True))
report=dict(status='PASS',scope='Independent complete expansion, uniqueness and coefficient queries on three small packets with ordinary and tied branches',cases=receipts)
(HERE/'EXPORTER_TEST_RECEIPT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
