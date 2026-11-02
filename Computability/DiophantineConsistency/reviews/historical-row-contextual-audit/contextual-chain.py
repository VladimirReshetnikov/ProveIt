#!/usr/bin/env python3
"""Explicit no-Lean contextual rerun of selected exact original parent audits."""
import contextlib,hashlib,importlib.util,io,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];REV=ROOT/'Computability/DiophantineConsistency/reviews';SELF=Path(__file__).resolve()
TARGETS={'row':('compact44-row-match-independent-audit','132d62eb41c5876d1612e7d7702993ce28f67f837e942758e45b6e5ee5993d06'),'lookup':('compact44-table-lookup-independent-audit','e8224dba8c94ed303bfd782cbc77b76ad574c11c216f692b4f4d2ce6e92474e1'),'relabel':('compact44-relabel-pair-independent-audit','dd920218d4bbc4e4d8b11f5262ad672964d2aede0cc24fee5b7b9816c207f909'),'permutation':('compact44-permutation-lookup-independent-audit','d78fd20710224a9f81ef2a6f67fc3403bf1ce1250d81698d615eec3c106896ba'),'endpoint':('thirteen-model-endpoint-successor-pair-independent-audit','ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681')}
EDGES={'row':{'lookup'},'lookup':{'relabel','permutation'},'relabel':{'endpoint'},'permutation':{'endpoint'},'endpoint':set()}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 if len(sys.argv)!=3 or sys.argv[1] not in TARGETS:raise ValueError('usage: target /tmp/ipra-historical-audit-review-*')
 target=sys.argv[1];view=Path(sys.argv[2]).resolve()
 if Path.cwd().resolve()!=ROOT.resolve() or view.parent!=Path('/tmp').resolve() or not view.name.startswith('ipra-historical-audit-review-'):raise ValueError('invalid cwd or historical view')
 directory,h=TARGETS[target];path=REV/directory/'audit.py'
 if sha(path)!=h:raise ValueError('original audit byte drift')
 plan=view/'Computability/DiophantineConsistency/reviews/thirteen-model-endpoint-closure-independent-audit'
 if sha(plan/'audit.py')!='30ccbcaa1050d3c9e6b9e4b73e930928fd93cba2380bba3ecdb629de755e587c' or sha(plan/'CHECK.json')!='ab2255186de1e61028731a47a1c92e89792835efe7317e4560b86861bc002af7' or sha(view/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ModelCarrierCurrent.lean')!='3f76453da57164d06bd338928d0e3d587df46851c77d5cbc4fbf858119719076':raise ValueError('historical view drift')
 sp=importlib.util.spec_from_file_location('original_'+target,path);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
 if target=='endpoint':m.PARENTAUDIT=plan
 class Proxy:
  def __getattr__(self,k):return getattr(subprocess,k)
  def run(self,cmd,*args,**kwargs):
   if isinstance(cmd,(list,tuple)) and cmd:
    for child in EDGES[target]:
     if str(cmd[-1])==str(REV/TARGETS[child][0]/'audit.py'):
      cmd=list(cmd[:-1])+[str(SELF),child,str(view)];break
   return subprocess.run(cmd,*args,**kwargs)
 m.subprocess=Proxy();buf=io.StringIO()
 with contextlib.redirect_stdout(buf):m.main()
 result=buf.getvalue()
 if json.loads(result)!=json.loads((REV/directory/'CHECK.json').read_bytes()):raise ValueError('complete audit output differs from pinned receipt')
 print(result,end='')
if __name__=='__main__':main()
