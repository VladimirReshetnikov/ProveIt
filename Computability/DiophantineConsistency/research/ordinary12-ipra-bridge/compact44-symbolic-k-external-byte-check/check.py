#!/usr/bin/env python3
"""External finite comparison only; not a Lean proof or model theorem."""
import hashlib,gzip,json,re,sys
from pathlib import Path
R=Path(__file__).resolve().parents[3]
files={
 'rows':('research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8'),
 'kernel':('research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean','f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae'),
 'param':('research/ordinary12-ipra-bridge/compact44-symbolic-kernel-param-prototype/CompactSymbolicKernelOpaque.lean','fbef8642de957bb39493607cb67edda418f53332af5a92ee594a2a437241e0b8'),
 'mass':('research/ordinary12-ipra-bridge/compact44-coefficient-mass-prototype/CompactCoefficientMass.lean','ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e'),
 'retained':('candidates/ten-positive-shifted-strong/coefficients/K.bin.gz','b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a')}
def require(b,msg):
 if not b:raise ValueError(msg)
require(__debug__ and not sys.flags.optimize,'optimized Python rejected')
def check():
 for name,(path,pin) in files.items():
  actual=hashlib.sha256((R/path).read_bytes()).hexdigest()
  require(actual==pin,'hash mismatch: '+name)
check()
text=(R/files['rows'][0]).read_text();b='-- BEGIN PINNED ORDERED ROWS\n';e='\n-- END PINNED ORDERED ROWS';require(text.count(b)==1 and text.count(e)==1,'row markers')
rows=[]
for i,line in enumerate(text.split(b)[1].split(e)[0].splitlines()):
 m=re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\)(,?)',line);require(m is not None,'row syntax');rows.append(tuple(map(int,m.group(1,2,3,4))));require(m.group(5)==(',' if i<942 else ''),'row comma')
require(len(rows)==943,'row count')
src=(R/files['kernel'][0]).read_text();m=re.search(r'^def slots : List ℕ := \[([0-9,]+)\]$',src,re.M);require(m is not None,'slot syntax');slots=list(map(int,m.group(1).split(',')));require(len(slots)==41 and len(set(slots))==41 and max(slots)<4393,'slot conditions')
P=lambda e:1<<(67*e)
def value(t):
 w,n,e,s=t;require(0<=w<256 and 0<=n<512 and 0<=e<256 and 0<=s<512,'field bound');return w+(1<<8)*n+(1<<17)*e+(1<<25)*s+127*(1<<34)
def reflected(e,c):return c*(P(4393-e)+P(5495-e))
k=sum(P(e) for e in (30,62,1100,2201))
k+=sum(reflected(i,1+(1<<10)*((1<<41)-value(row))) for i,row in enumerate(rows))
k+=sum(reflected(e,1<<(10+j)) for j,e in enumerate(slots))
k+=P(8807)*P(42)
raw=k.to_bytes((k.bit_length()+7)//8,'little');expected=gzip.decompress((R/files['retained'][0]).read_bytes());rawhash=hashlib.sha256(raw).hexdigest()
require(raw==expected,'symbolic recipe does not equal retained bytes');require(rawhash=='c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e','wrong original payload')
check(); print(json.dumps({'status':'PASS_EXTERNAL_SYMBOLIC_RECIPE_BYTES','rows':len(rows),'slots':len(slots),'raw_bytes':len(raw),'raw_sha256':rawhash,'bit_length':k.bit_length(),'scope':'external Python, not an internal equality or model theorem'},sort_keys=True))
