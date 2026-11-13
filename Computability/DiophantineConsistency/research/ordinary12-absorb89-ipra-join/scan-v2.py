#!/usr/bin/env python3
"""Compare the actual 89-halt serialized project closure with the 90 iPRA union."""
from pathlib import Path
from hashlib import sha256
import importlib.util,json,os,sys,traceback
H=Path(__file__).resolve().parent;D=H.parents[1]
R=D/'research/ordinary12-direct90-ipra-join/run-v9.py'
P=D/'research/ordinary12-absorb89-probe/observations/halt-attempt01/result.json'
Q=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
OBS=H/'observations/scan-attempt02'
if OBS.exists():raise SystemExit('refusing to overwrite')
def sh(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
need(sh(R)=='117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03','runner pin')
need(sh(P)=='394ff5eb91126c7c879c07d215a959e3899bbe4db1e157727c373d67e8e73cb3','halt pin')
need(sh(Q)=='09430817390268544ed668c691d9aaf335c68b85386c2acb6a3d7b1d76f239ed','90 join pin')
s=importlib.util.spec_from_file_location('reviewedv9',R);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
need(sh(m.LEAN)==m.PINS[m.LEAN] and sh(m.HELPER)==m.PINS[m.HELPER] and sh(m.INVENTORY)==m.PINS[m.INVENTORY],'tool pin')
halt=json.loads(P.read_text());join=json.loads(Q.read_text());need(halt['status']=='PASS' and join['status']=='PASS','prior status')
paths=[Path(x) for x in halt['lean_path'].split(':')[:-1]];out=Path(join['output_root'])/'lib'
inv=json.loads(m.INVENTORY.read_text());known=set(inv['objects'])
for base in paths:
 for o in base.glob('*.olean'):known.add(o.stem)
known.add('Absorb89Halt')
env={'PATH':'/usr/bin:/bin','LEAN_PATH':halt['lean_path'],'LEAN_NUM_THREADS':'1'}
OBS.mkdir(parents=True);result={'status':'FAILED','halt_result_sha256':sh(P),'prior_join_sha256':sh(Q),'scanner_sha256':sh(__file__),'scope':'selected serialized project closure and direct outside companions only; not package-transitive or source-object replay'}
try:
 c=m.scan_closure(['Absorb89Halt'],paths,env,OBS,'selected',known)
 missing=[];mismatch=[];matched=[]
 for n,row in c['project'].items():
  stem=out/m.relative_module(n);other={suffix:m.rec(str(stem)+suffix) for suffix in m.SUFFIXES}
  if other['.olean'] is None:missing.append(n)
  elif any((None if row['companions'][x] is None else row['companions'][x]['sha256']) != (None if other[x] is None else other[x]['sha256']) for x in m.SUFFIXES):mismatch.append(n)
  else:matched.append(n)
  row['join_provider']=other
 m.recheck_outside(c)
 for n,row in c['project'].items():
  stem=str(row['path'])[:-len('.olean')];need(m.rec(row['path'])==row['record'] and {x:m.rec(stem+x) for x in m.SUFFIXES}==row['companions'],'project drift '+n)
  target=out/m.relative_module(n);need({x:m.rec(str(target)+x) for x in m.SUFFIXES}==row['join_provider'],'join provider drift '+n)
 need(sh(m.LEAN)==m.PINS[m.LEAN] and sh(m.HELPER)==m.PINS[m.HELPER] and sh(m.INVENTORY)==m.PINS[m.INVENTORY],'tool drift')
 need(sh(__file__)==result['scanner_sha256'],'scanner drift')
 need(sh(R)=='117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03' and sh(P)==result['halt_result_sha256'] and sh(Q)==result['prior_join_sha256'],'input drift')
 result.update(status='PASS',closure=c,report={'selected':len(c['project']),'outside':len(c['outside']),'matched':sorted(matched),'missing':sorted(missing),'mismatched':sorted(mismatch)})
except Exception as e:result.update(error=repr(e),traceback=traceback.format_exc())
(OBS/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'error':result.get('error'),'counts':{k:len(v) if isinstance(v,list) else v for k,v in result.get('report',{}).items()}}))
if result['status']!='PASS':sys.exit(1)
