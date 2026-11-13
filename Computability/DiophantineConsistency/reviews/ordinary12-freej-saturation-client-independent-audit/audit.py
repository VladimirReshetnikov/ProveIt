#!/usr/bin/env python3
"""Independent artifact audit of the paired conditional saturation proof."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';PKG=RESEARCH/'free-j-saturation-client-prototype'
OUT=Path('/tmp/ipra-freej-saturation-client-pair-01');PREFIX=Path('/tmp/ipra-freej-population-client-pair-02');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PLAN=RESEARCH/'free-j-saturation-closure-plan';PARENT=BASE/'reviews/ordinary12-freej-population-client-independent-audit';PLAN_AUDIT=BASE/'reviews/ordinary12-freej-saturation-closure-independent-audit';PRE=BASE/'reviews/ordinary12-freej-saturation-client-prelaunch-audit'
R='9cc65ff7252482a916a3f80f9f5a8767d3ece8b874b7f3e4a93b11504d560e0c';DRIVER='05e5563e0eaf17f7beb6a6e0b5412159b488c12fa615806d85b8678cef917d3f'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','33f69b2663','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len([x for x in names if '/evidence/' in x and x.endswith('.log')])==10,'tracked log count')
 for name in names:
  blob=subprocess.run(['git','show','33f69b2663:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'committed drift '+name)
 need(sha(PKG/'replay.py')==DRIVER and sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==R,'driver/receipt')
 term=(PKG/'evidence/terminal.txt').read_text();need('session 46258 exit 0' in term and '8750eed704e41c19d002fd77868a8bb8977232a5' in term and term.rstrip().endswith('PASS_PAIRED_FREEJ_SATURATION_CLIENT '+R),'outer observation')
 rec=json.loads((PKG/'evidence/receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_FREEJ_SATURATION_CLIENT' and len(rec['runs'])==2,'receipt status')
 for path,h in rec['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed input '+path)
 need(sha(PRE/'CHECK.json')=='849ebddc37af6fee51eae9fcd9ab0481d17f4776a4c3dd3d709c9fa9d73e5380' and json.loads((PRE/'CHECK.json').read_bytes())['driver_sha256']==DRIVER,'prelaunch audit')
 for directory in (PARENT,PLAN_AUDIT):
  q=subprocess.run([sys.executable,'-I','-S','-B',str(directory/'audit.py')],capture_output=True,timeout=900)
  need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((directory/'CHECK.json').read_bytes()),'parent audit '+str(directory))
 need(rec['population_audit']==json.loads((PARENT/'CHECK.json').read_bytes()),'population audit receipt')
 scan=json.loads((PLAN/'scan.json').read_bytes());rows=scan['modules'];need(len(rows)==4,'four source closure')
 modules=[r['module'] for r in rows]+['DiophantineConsistency.FreeJSaturationClient'];src_hash={r['module']:r['source_sha256'] for r in rows};src_hash[modules[-1]]=rec['fixed_inputs_sha256'][str(PKG/'FreeJSaturationClient.lean')]
 allruns=[]
 for run,side in zip(rec['runs'],('author','peer')):
  need(run['label']==side and [s['module'] for s in run['steps']]==modules,'module order')
  lib=OUT/side/'lib';base=PREFIX/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path(*n.split('.')).with_suffix('.olean') for n in modules}
  need(len(orig)==109 and not orig&extra and actual==orig|extra,'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'provider object '+str(rel))
  available=set(orig);checked=[]
  for ix,step in enumerate(run['steps']):
   name=step['module'];rel=Path(*name.split('.'));src=OUT/'frozen'/rel.with_suffix('.lean');obj=lib/rel.with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');copy=PKG/'evidence'/side/log.name
   need(step['compiler_exit']==step['deps_exit']==0 and step['stop_reason'] is None,'exits '+name)
   need(sha(src)==step['source_sha256']==src_hash[name] and sha(obj)==step['object_sha256'] and sha(log)==sha(copy)==step['log_sha256'] and log.read_text()==step['stdout'],'artifacts '+name)
   cmd=step['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command '+name)
   imports=[v for line in src.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
   if ix<4:need(imports==rows[ix]['imports'],'source import list '+name)
   deps={str(PACKAGE/'Init.olean')}
   for dep in imports:
    drel=Path(*dep.split('.')).with_suffix('.olean')
    if dep.startswith('DiophantineConsistency.'):
     need(drel in available,'same-side missing at step '+name+':'+dep);candidate=lib/drel
    elif drel in available:candidate=lib/drel
    else:candidate=PACKAGE/drel
    need(candidate.is_file(),'import object '+dep);deps.add(str(candidate))
   need(set(step['deps_stdout'].splitlines())==deps,'direct deps '+name)
   reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",step['stdout'],re.M)
   wanted=['FreeJSaturationClient.graph_saturation'] if name==modules[-1] else []
   need([n for n,_ in reports]==wanted and [[n,a] for n,a in reports]==step['axiom_reports'],'named report '+name)
   need(all({x.strip() for x in a.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,a in reports),'axiom set '+name)
   if name==modules[0]:
    warning=(f"{src}:153:12: warning: try 'simp' instead of 'simpa'\n\nNote: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n"
      f"{src}:159:16: warning: try 'simp' instead of 'simpa'\n\nNote: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n"
      f"{src}:153:54: warning: 'simp' tactic does nothing\n\nNote: This linter can be disabled with `set_option linter.unusedTactic false`\n"
      f"{src}:153:54: warning: this tactic is never executed\n\nNote: This linter can be disabled with `set_option linter.unreachableTactic false`\n")
    need(step['stdout']==warning,'exact four allowed warnings')
   else:need('warning:' not in step['stdout'],'unexpected warning '+name)
   need('error:' not in step['stdout'] and 'sorryAx' not in step['stdout'],'error/sorry '+name)
   available.add(rel.with_suffix('.olean'));checked.append({'module':name,'source_sha256':step['source_sha256'],'object_sha256':step['object_sha256'],'log_sha256':step['log_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
  allruns.append({'side':side,'steps':checked})
 need(allruns[0]['steps']==allruns[1]['steps'],'sibling outputs differ')
 print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_SATURATION_CLIENT_AUDIT','evidence_commit':'33f69b2663','receipt_sha256':R,'recorded_outer_session':46258,'recorded_outer_exit':0,'reported_launch_head':'8750eed704e41c19d002fd77868a8bb8977232a5','parent_audits_rerun':2,'steps_per_side':5,'allowed_warnings_per_side':4,'runs':allruns,'scope':'Conditional IΣ₁ model graph saturation under explicit radix, split, mask-population and graph premises; no compact44 port binding, checker, machine simulation or iPRA; inherited provider/resource limitations.'},indent=2))
if __name__=='__main__':main()
