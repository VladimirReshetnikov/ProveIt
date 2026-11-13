#!/usr/bin/env python3
"""Restore only four pinned compact44 gzip payloads to their declared P13 paths."""
import gzip,hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];B=D/'con-zfc-diophantine-forms/72-congruence-sextic';S=D/'con-zfc-diophantine-forms/44-b4-sparse/native/coefficients';dst=B/'positive13/native/coefficients';HERE=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
a=(B/'positive13/ACTIVE_BINDING.json').read_bytes();b=(B/'positive14/ACTIVE_BINDING.json').read_bytes();need(sha(a)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(b)=='f3ebbe2956482e2965c286d4a2cc648b99106e3e3859f1feb6cbebae820dc2ec','binding pins');p=json.loads(a);q=json.loads(b);names=['beta','K0','MC','MF'];need(not dst.exists(),'destination existed before restoration')
inputs={};pre={}
for n in names:
 x=p['ports'][n];y=q['ports'][n];need(all(x[k]==y[k] for k in ('encoding','bits','raw_bytes','sha256_raw','sha256_gzip')),'binding disagreement '+n)
 expected=(B/'positive13'/x['path']).resolve();other=(B/'positive14'/y['path']).resolve();need(expected==other==dst/Path(x['path']).name and not expected.exists(),'path/absence '+n)
 data=(S/expected.name).read_bytes();raw=gzip.decompress(data);need(sha(data)==x['sha256_gzip'] and sha(raw)==x['sha256_raw'] and len(raw)==x['raw_bytes'] and int.from_bytes(raw,'little').bit_length()==x['bits'] and raw[-1]!=0,'source payload '+n)
 inputs[n]=data;pre[n]={'declared_path':str(expected),'exists_before':False,'source_path':str((S/expected.name).resolve()),'gzip_sha256':sha(data),'raw_sha256':sha(raw),'raw_bytes':len(raw),'bits':x['bits']}
ob=HERE/'before.json';need(not ob.exists(),'observation exists');ob.write_text(json.dumps({'status':'PASS_FOUR_ABSENT_VERIFIED_SOURCE_BYTES','ports':pre,'scope':'before restoration; no original binding metadata created'},indent=2,sort_keys=True)+'\n')
dst.mkdir()
for n in names:
 path=Path(pre[n]['declared_path'])
 with path.open('xb') as f:f.write(inputs[n])
 data=path.read_bytes();raw=gzip.decompress(data);need(sha(data)==pre[n]['gzip_sha256'] and sha(raw)==pre[n]['raw_sha256'] and len(raw)==pre[n]['raw_bytes'] and int.from_bytes(raw,'little').bit_length()==pre[n]['bits'],'postwrite '+n)
print(json.dumps({'status':'PASS_FOUR_FILES_RESTORED_AND_VERIFIED','before_sha256':sha(ob.read_bytes()),'ports':pre,'scope':'Only four gzip files restored from matching tracked source44 bytes; no original binding metadata created.'},indent=2,sort_keys=True))
