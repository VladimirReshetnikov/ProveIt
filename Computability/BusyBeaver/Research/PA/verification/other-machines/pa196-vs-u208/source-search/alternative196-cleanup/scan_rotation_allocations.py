#!/usr/bin/env python3
"""Single-global-rotation search: startup-protected allocation, no fresh states."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
from collections import Counter
import scan_rotations as s, verify_second_cleanup as cleanup
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);ap.add_argument('--winner-dir',type=Path);ap.add_argument('--seconds',type=int,default=2);args=ap.parse_args()
root=cleanup.patch(s,s.root,cleanup.PARENT_FIRST,('dec',1),[3773,3774,3775]);base=s.graph(root)
ops={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'};variants={}
for tree,(node,direction,replacement) in s.allrot(root):
 if s.metric(tree)>160 or tree in variants:continue
 if s.graph(tree)!=base:raise ValueError('rotation changed ordinal CFG')
 rows=[[''.join(map(str,path)),ops[s.store[leaf][0]],None if s.store[leaf][0]=='halt' else s.store[leaf][1]] for path,leaf in s.leaf_occurrences(tree)]
 if rows[25][0]!='100000':continue
 variants[tree]=(node,direction,replacement,rows)
if len(variants)!=59:raise ValueError('unexpected number of screened rotations')
print('qualifying rotations:',len(variants),flush=True)
results=[]
with tempfile.TemporaryDirectory(prefix='pa-alt196-rotations-') as tmp:
 for i,(tree,(node,direction,replacement,rows)) in enumerate(variants.items()):
  inp=Path(tmp)/'source.json';data=(json.dumps(rows,separators=(',',':'))+'\n').encode();inp.write_bytes(data);out=Path(tmp)/'output';out.mkdir(exist_ok=True)
  cmd=[sys.executable,str(HERE/'allocate.py'),str(inp),str(out),'--protected',str(HERE/'protected-startup.txt'),'--seconds',str(args.seconds),'--feasible-only','--fresh','0']
  run=subprocess.run(cmd,capture_output=True,text=True)
  if run.returncode:raise RuntimeError(run.stderr)
  rec=json.loads((out/'allocation.json').read_text());results.append({'index':i,'status':rec['status'],'solver':rec.get('solver'),'states':rec.get('states'),'direction':direction,'node_id':node,'source_sha256':hashlib.sha256(data).hexdigest()})
  if rec.get('states',196)<196:
   if args.winner_dir is None:raise RuntimeError('candidate found; rerun with --winner-dir to preserve it')
   args.winner_dir.mkdir(parents=True,exist_ok=True);(args.winner_dir/'source.json').write_bytes(data);(args.winner_dir/'candidate.native.tm').write_bytes((out/'candidate.native.tm').read_bytes());(args.winner_dir/'allocation.json').write_text(json.dumps(rec,indent=2)+'\n');print('candidate',results[-1],flush=True);break
  if (i+1)%10==0:print('checked',i+1,'/',len(variants),flush=True)
args.output.write_text(json.dumps({'source_program_sha256':hashlib.sha256((HERE/'Program.lean').read_bytes()).hexdigest(),'scope':'all distinct single global rotations with <=160 internal nodes and seed path 100000; startup-protected allocator, no fresh labels','solver_timeout_seconds':args.seconds,'results':results},indent=2)+'\n')
print('results',dict(Counter(x['status'] for x in results)),flush=True)
