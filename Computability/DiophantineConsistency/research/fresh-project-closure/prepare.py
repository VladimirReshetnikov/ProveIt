#!/usr/bin/env python3
"""Freeze an authenticated source-declared project import closure; does not compile."""
import argparse,hashlib,json,re,subprocess,tomllib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--target',default='DiophantineConsistency.IPRAAQ29NativeChecks');a=p.parse_args()
out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);src=out/'src';src.mkdir()
config=ROOT/'lakefile.toml';cfg=tomllib.loads(config.read_text());libs={x['name']:ROOT/x.get('srcDir','.') for x in cfg['lean_lib']};libs.pop('Foundation',None)
# Lean imports occur in the header. Strip nested comments and line comments,
# preserving newlines so ordinary import declarations are read as whole lines.
def uncomment(s):
 out=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:
    if s[i]=='\n':out.append('\n')
    i+=1
  elif s.startswith('/-',i):depth=1;i+=2
  elif s.startswith('--',i):
   while i<len(s) and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 if depth:raise ValueError('unclosed nested comment')
 return ''.join(out)
rows={};external=set();visiting=set();order=[]
def visit(name):
 if name in rows or name in external:return
 if name in visiting:raise ValueError(('cycle',name))
 top=name.split('.')[0]
 if top not in libs:external.add(name);return
 path=libs[top]/(name.replace('.','/')+'.lean')
 if not path.is_file():raise FileNotFoundError((name,str(path)))
 raw=path.read_bytes();text=raw.decode();deps=[]
 for line in uncomment(text).splitlines():
  m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$',line)
  if m:
   names=m.group(1).split()
   if not names or any(not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\'.]*',x) for x in names):raise ValueError(('unsupported import syntax',name,line))
   deps.extend(names)
 visiting.add(name)
 for d in deps:visit(d)
 visiting.remove(name)
 snapshot=src/(name.replace('.','/')+'.lean');snapshot.parent.mkdir(parents=True,exist_ok=True);snapshot.write_bytes(raw)
 digest=hashlib.sha256(raw).hexdigest()
 if H(snapshot)!=digest or H(path)!=digest:raise RuntimeError(('source changed while freezing',name))
 rows[name]={'workspace_path':str(path.relative_to(ROOT)),'snapshot_path':str(snapshot.relative_to(out)),'sha256':digest,'imports':deps};order.append(name)
try:
 visit(a.target)
 for name,row in rows.items():
  if H(ROOT/row['workspace_path'])!=row['sha256'] or H(out/row['snapshot_path'])!=row['sha256']:raise RuntimeError(('source drift before manifest',name))
 m={'status':'FROZEN_NOT_COMPILED','target':a.target,'root':str(ROOT),'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'lakefile_sha256':H(config),'lean_toolchain_sha256':H(ROOT/'lean-toolchain'),'project_modules':len(order),'order':order,'sources':rows,'external_modules':sorted(external),'scope':'Source-declared project import graph and point-in-time workspace hashes only; not Lean compilation, package-transitive provenance, dynamic import accounting or proof replay.'}
 (out/'manifest.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n')
 print('FROZEN_NOT_COMPILED',len(order),'project modules',len(external),'direct external modules',H(out/'manifest.json'),flush=True)
except BaseException as e:
 (out/'failure.txt').write_text(repr(e)+'\n');raise
