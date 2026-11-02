#!/usr/bin/env python3
"""Independent source-declared closure and point-in-time provider check; no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PLAN=BASE/'research/ordinary12-ipra-bridge/free-j-population-closure-plan'
FREE=Path('/tmp/ipra-freej-power-finish-pair-01');END=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
POWER=BASE/'reviews/ordinary12-freej-power-finish-independent-audit/CHECK.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def tree(base):return {p.relative_to(base):p for p in base.rglob('*.olean')}
def main():
 prefix=PLAN.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','9c04a203e2','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len(names)==3,'plan inventory')
 for name in names:
  blob=subprocess.run(['git','show','9c04a203e2:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'plan bytes '+name)
 normal=subprocess.run([sys.executable,'-I','-S',str(PLAN/'scan.py')],capture_output=True,timeout=60)
 opt=subprocess.run([sys.executable,'-O','-I','-S',str(PLAN/'scan.py')],capture_output=True,timeout=60)
 need(normal.returncode==0 and not normal.stderr and normal.stdout==(PLAN/'scan.json').read_bytes(),'normal scan')
 need(opt.returncode!=0 and b'optimized Python rejected' in opt.stderr,'optimized rejection')
 scan=json.loads(normal.stdout);need(scan['status']=='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','scan status')
 sourcepaths={}
 for folder in (BASE/'Lean/DiophantineConsistency',BASE/'research/ordinary12-ipra-bridge'):
  for p in folder.rglob('*.lean'):sourcepaths.setdefault(p.stem,[]).append(p)
 def verify_closure(sidebase,rows,target,expected_count):
  need(len(rows)==expected_count,'closure count')
  modules=[row['module'] for row in rows];need(len(set(modules))==len(modules) and modules[-1]==target,'unique target')
  lookup={row['module']:row for row in rows}; visited=set();order=[]; leaves=set()
  def visit(module):
   if module in visited:return
   visited.add(module);rel=Path(*module.split('.')).with_suffix('.olean')
   if (sidebase/rel).is_file() or (PKG/rel).is_file():leaves.add(module);return
   need(module in lookup,'omitted unresolved module '+module)
   row=lookup[module];opts=sourcepaths.get(module.split('.')[-1],[])
   need(len(opts)==1 and str(opts[0])==row['source'],'source identity '+module)
   p=opts[0];need(sha(p)==row['source_sha256'],'source hash '+module)
   lines=p.read_text().splitlines();need(not any(re.match(r'^\s+import\s',line) for line in lines),'indented import '+module)
   imports=[item for line in lines if line.startswith('import ') for item in line[7:].split()]
   need(imports==row['imports'],'imports '+module)
   for dep in imports:visit(dep)
   order.append(module)
  visit(target)
  need(order==modules and set(order)==set(lookup),'topology/reachability')
  return len(leaves)
 preferred=scan['preferred_rebuild'];alternative=scan['alternative_rebuild']
 leaf_counts={}
 for side in ('author','peer'):
  leaf_counts[side]=[verify_closure(FREE/side/'lib',preferred,'DiophantineConsistency.ArithmeticHalfBinomialCompat',9),verify_closure(END/side/'lib',alternative,'DiophantineConsistency.FreeJPowerFinish',33)]
  source=tree(FREE/side/'lib');records=scan['freej_base_objects'];need(len(source)==len(records)==97,'base count')
  need({str(x) for x in source}=={x['module_path'] for x in records},'base paths')
  for row in records:
   f=source[Path(row['module_path'])]
   need(sha(f)==row['sha256'] and str(f.resolve())==row[side+'_resolved_path'],'base object '+row['module_path'])
  endpoint=tree(END/side/'lib');shared=source.keys()&endpoint.keys()
  diffs=sorted(str(p) for p in shared if sha(source[p])!=sha(endpoint[p]))
  need(len(shared)==64 and diffs==['BusyBeaver/ZFC/KZip.olean','DiophantineConsistency/ModelDifferenceRing.olean'],'actual provider differences')
  power=json.loads(POWER.read_bytes());row=next(r for r in power['runs'] if r['side']==side);seed=FREE/side/'FreeJPowerFinish.olean'
  need(sha(POWER)=='1f0357d7cb23f09fe6079e5ee744f7cf8cab6bd06d96b6e80b3167fbc9c86d7b' and sha(seed)==row['object_sha256']==scan['freej_power_seed'][side]['sha256'],'power seed')
 print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_POPULATION_CLOSURE_SOURCE_AUDIT','plan_commit':'5d45113961','wording_correction_commit':'9c04a203e2','normal_scan_exit':normal.returncode,'optimized_scan_exit':opt.returncode,'freej_objects_per_side':97,'shared_provider_objects_per_side':64,'differing_objects':['BusyBeaver/ZFC/KZip.olean','DiophantineConsistency/ModelDifferenceRing.olean'],'preferred_modules':9,'alternative_modules':33,'resolved_leaf_counts':leaf_counts,'scope':'Point-in-time source-declared import and provider inventory only; no simultaneous freeze, Lean build, graph application, package-transitive/dynamic closure or iPRA proof.'},indent=2))
if __name__=='__main__':main()
