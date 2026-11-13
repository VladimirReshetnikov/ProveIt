#!/usr/bin/env python3
"""Freeze a tracked, source-current coexistence closure. No Lean compilation."""
import argparse,hashlib,json,re,subprocess,tomllib
from pathlib import Path
if not __debug__:raise RuntimeError('guards require Python assertions enabled')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[5]
TARGET='DiophantineConsistency.FreeJProviderChecks'
OVERRIDES={
 'DiophantineConsistency.FreeJProviderChecks':HERE/'FreeJProviderChecks.lean',
 'DiophantineConsistency.FreeJNormZero':HERE.parents[1]/'free-j-ordinary-descent-prototype/FreeJNormZero.lean',
 'DiophantineConsistency.Ordinary12FreeJ':HERE.parents[1]/'free-j-prototype/Ordinary12FreeJ.lean',
 'DiophantineConsistency.Ordinary12Patterns':HERE.parents[1]/'concrete-split-prototype/Ordinary12Patterns.lean',
 'DiophantineConsistency.Ordinary12FactorSplit':HERE.parents[1]/'model-prototype/Ordinary12FactorSplit.lean',
 'DiophantineConsistency.Ordinary12Residual':HERE.parents[1]/'model-prototype/Ordinary12Residual.lean',
}
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def validate_output(path,protected):
 """Reject existing paths, symlink ancestors and either-way root overlap."""
 out=Path(path).absolute()
 if out.exists() or out.is_symlink():raise ValueError(('existing output',str(out)))
 for parent in out.parents:
  if parent.is_symlink():raise ValueError(('symlink output ancestor',str(parent)))
 resolved=out.resolve(strict=False)
 if resolved!=out:raise ValueError(('noncanonical output',str(out)))
 for root in protected:
  root=Path(root).resolve(strict=False)
  if resolved.is_relative_to(root) or root.is_relative_to(resolved):
   raise ValueError(('output/protected overlap',str(resolved),str(root)))
 return resolved
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
 if depth:raise ValueError('unclosed comment')
 return ''.join(out)
def imports(raw):
 result=[]
 for line in uncomment(raw.decode()).splitlines():
  m=re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+?)\s*$',line)
  if m:
   ns=m.group(1).split()
   if not ns or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*",x) for x in ns):raise ValueError(('unsupported import',line))
   result.extend(ns)
 return result
def walk(target,read,is_project):
 rows={};external=set();visiting=set();order=[]
 def visit(n):
  if n in rows or n in external:return
  if n in visiting:raise ValueError(('cycle',n))
  if not is_project(n):external.add(n);return
  path,raw=read(n);deps=imports(raw);visiting.add(n)
  for d in deps:visit(d)
  visiting.remove(n);rows[n]={'path':path,'raw':raw,'imports':deps};order.append(n)
 visit(target)
 return rows,order,sorted(external)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 protected=[ROOT,Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun'),
  Path('/tmp/ipra-aq29-fresh-project-pair'),Path('/tmp/ipra-aq29-fresh-source-closure-v2'),
  Path('/tmp/ipra-model-diff-closure-plan-01'),Path('/tmp/ipra-ordinary12-coexistence-source-01'),
  Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0')]
 protected.extend(p for p in Path('/tmp').glob('ipra-ordinary12-coexistence-source-*') if p.is_dir())
 out=validate_output(a.output,protected)
 cfg=ROOT/'lakefile.toml';libs={x['name']:ROOT/x.get('srcDir','.') for x in tomllib.loads(cfg.read_text())['lean_lib']};libs.pop('Foundation',None)
 head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();cfg_hash=H(cfg);tool_hash=H(ROOT/'lean-toolchain')
 def read(n):
  expected=libs[n.split('.')[0]]/(n.replace('.','/')+'.lean');path=OVERRIDES.get(n,expected)
  if n in OVERRIDES and (expected.exists() or expected.is_symlink()):raise ValueError(('shadowed override',n,str(expected)))
  if not path.is_file() or path.is_symlink():raise ValueError(('missing or symlink source',n,str(path)))
  rel=path.relative_to(ROOT);raw=path.read_bytes()
  committed=subprocess.run(['git','show',head+':'+str(rel)],cwd=ROOT,capture_output=True)
  if committed.returncode or committed.stdout!=raw:raise ValueError(('not exact tracked Git blob',n,str(rel)))
  return str(rel),raw
 rows,order,external=walk(TARGET,read,lambda n:n.split('.')[0] in libs)
 if len(order)!=len(set(order)) or order[-1]!=TARGET:raise ValueError('bad order')
 # This narrow compatibility endpoint is deliberately expected to match the
 # surveyed 64 project + 5 existing research + one checks source closure.
 if len(order)!=70:raise ValueError(('unexpected closure count; re-audit imports',len(order)))
 if validate_output(out,protected)!=out:raise ValueError('output changed before creation')
 out.mkdir(parents=True)
 if out.is_symlink() or out.resolve(strict=True)!=out:raise ValueError('output changed during creation')
 src=out/'src';src.mkdir();source_rows={}
 for n in order:
  row=rows[n];dest=src/(n.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(row['raw']);digest=hashlib.sha256(row['raw']).hexdigest()
  if H(dest)!=digest or H(ROOT/row['path'])!=digest:raise ValueError(('source drift while freezing',n))
  source_rows[n]={'workspace_path':row['path'],'snapshot_path':str(dest.relative_to(out)),'sha256':digest,'imports':row['imports']}
 for n,row in source_rows.items():
  if H(ROOT/row['workspace_path'])!=row['sha256'] or H(out/row['snapshot_path'])!=row['sha256']:
   raise ValueError(('source drift before manifest',n))
 if subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()!=head or H(cfg)!=cfg_hash or H(ROOT/'lean-toolchain')!=tool_hash:raise ValueError('HEAD or config changed')
 manifest={'status':'FROZEN_NOT_COMPILED','target':TARGET,'root':str(ROOT),'head':head,'lakefile_sha256':cfg_hash,'lean_toolchain_sha256':tool_hash,'project_modules':len(order),'order':order,'sources':source_rows,'external_modules':external,'scope':'Tracked source-declared graph only, endpoint checks coexistence not graph transport, ordinary integrality or iPRA proof; no Lean compilation.'}
 (out/'manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
 print('FROZEN_NOT_COMPILED',len(order),'project modules',len(external),'external modules',H(out/'manifest.json'),flush=True)
if __name__=='__main__':main()
