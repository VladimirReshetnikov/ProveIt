#!/usr/bin/env python3
"""Capture selected serialized closure of the full displayed BFS client."""
from pathlib import Path
from hashlib import sha256
import importlib.util,json,os,sys,traceback
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
h=Path(__file__).resolve().parent;d=h.parents[1];base=d/'research/ordinary12-direct90-ipra-join/run-v9.py';rootrec=d/'research/ten-positive-80-bfs-displayed-full-ipra/observations/attempt01/terminal.json';rootrun=d/'research/ten-positive-80-bfs-displayed-full-ipra/run.py';replay=d/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json';obs=h/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
pins={base:'117ca7e29a4822832ffbe8a213431c89c770f1f51ddaa9ee11efee4b7fe15f03',rootrec:'bd210ff5388f1353c65821031bde96e55a42ed20dac592ad42fe5a5943092ece',rootrun:'8df6e5de35cbf87fca96015e074fa62787ae3b5ec2f0b7ad17b278b14a633af8',replay:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559'}
for p,x in pins.items():need(sha(p)==x,'pin mismatch '+str(p))
need(not os.path.lexists(obs),'attempt exists');r=json.loads(rootrec.read_text());old=json.loads(replay.read_text());need(r['status']=='PASS' and old['status']=='PASS','input status')
for p,rec in r['pins'].items():need(sha(p)==rec['sha256'] and str(Path(p).resolve())==rec['resolved'],'selected input drift '+p)
root=Path(r['output']);need(sha(root)==r['output_sha256']=='74ec93c2bf96e2dbab51c271943c9c4e50502b5ab6440f8b7b23e0aa71406f85','root changed')
paths=[root.parent]+[Path(x) for x in ['/tmp/bfs-low-inferred-ys8rrjp6','/tmp/bfs-printed-high-9cpcolrs','/tmp/bfs-printed-beta-sjarp8v0','/tmp/bfs-high-symbolic-85ibqx1z','/tmp/bfs-high-flat-ygaljyep','/tmp/bfs-high-runs-95e4auty','/tmp/bfs-high-generic-nsp2g8fz','/tmp/bfs-printed-ipra-9m_nfq32','/tmp/bfs-printed-slots-qwdduxw9','/tmp/bfs-printed-kernel-orsko0l9','/tmp/bfs-printed-selectors-4w6qxofm','/tmp/direct-bfs-80-coherent-8gret5ed/lib']]
spec=importlib.util.spec_from_file_location('reviewed_v9',base);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
for p in (m.LEAN,m.HELPER,m.INVENTORY):need(sha(p)==m.PINS[p],'reader tool drift '+str(p))
known=set(json.loads(m.INVENTORY.read_text())['objects'])|set(old['closure']['project'])|set(old['built'])
for x in paths:
 need(x.is_dir(),'missing selected path '+str(x));known.update(p.stem for p in x.glob('*.olean'))
env={'PATH':'/usr/bin:/bin','LEAN_PATH':':'.join(map(str,paths))+':'+str(m.PACKAGE),'LEAN_NUM_THREADS':'1'}
obs.mkdir(parents=True);result={'status':'FAILED','pins':{str(k):v for k,v in pins.items()},'scanner_sha256':sha(__file__),'paths':[str(x) for x in paths], 'scope':'captured serialized project closure and direct outside records; inherited historical, supplemental, package-transitive and dynamic ancestry excluded'}
try:
 closure=m.scan_closure(['BFSDisplayedFullIPRA'],paths,env,obs,'selected',known);m.recheck_outside(closure)
 prior=old['closure']['project'];outside=old['closure']['outside'];matches=[];new=[];mismatch=[]
 for n,row in closure['project'].items():
  stem=str(row['path'])[:-6];need(m.rec(row['path'])==row['record'] and {x:m.rec(stem+x) for x in m.SUFFIXES}==row['companions'],'current selection drift '+n)
  if n in prior:
   if row['imports']!=prior[n]['imports'] or row['companions']!=prior[n]['companions']:mismatch.append(n)
   else:matches.append(n)
  else:new.append(n)
 outside_mismatch=[n for n,row in closure['outside'].items() if n not in outside or row['companions']!=outside[n]['companions']]
 for p,x in pins.items():need(sha(p)==x,'final pin drift '+str(p))
 for p,rec in r['pins'].items():need(sha(p)==rec['sha256'] and str(Path(p).resolve())==rec['resolved'],'final selected input drift '+p)
 need(sha(root)==r['output_sha256'],'root drift')
 result.update(status='PASS_CAPTURE',closure=closure,matched_prior=matches,new_project=new,mismatched_prior=mismatch,outside_mismatch=outside_mismatch,report={'project_count':len(closure['project']),'outside_count':len(closure['outside']),'matched_prior':len(matches),'new_project':len(new),'mismatched_prior':len(mismatch),'outside_mismatch':len(outside_mismatch),'header_batches':closure['header_batches']})
except Exception as e:result.update(error=repr(e),traceback=traceback.format_exc())
(obs/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':result['status'],'error':result.get('error'),'report':result.get('report')}),flush=True)
if result['status']!='PASS_CAPTURE':sys.exit(1)
