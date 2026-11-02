#!/usr/bin/env python3
"""Independent four-module source closure/provider review, no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';PLAN=RESEARCH/'free-j-saturation-closure-plan';CLIENT=RESEARCH/'free-j-saturation-client-prototype/FreeJSaturationClient.lean'
PARENT=BASE/'reviews/ordinary12-freej-population-client-independent-audit';PREFIX=Path('/tmp/ipra-freej-population-client-pair-02');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 files=[*(PLAN/x for x in ('README.md','scan.py','scan.json')),CLIENT]
 for p in files:
  name=p.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','e2ffe09c90:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(p),'committed bytes '+name)
 normal=subprocess.run([sys.executable,'-I','-S',str(PLAN/'scan.py')],capture_output=True,timeout=60)
 opt=subprocess.run([sys.executable,'-O','-I','-S',str(PLAN/'scan.py')],capture_output=True,timeout=60)
 need(normal.returncode==0 and not normal.stderr and normal.stdout==(PLAN/'scan.json').read_bytes(),'normal scan')
 need(opt.returncode!=0 and b'optimized Python rejected' in opt.stderr,'optimized guard')
 scan=json.loads(normal.stdout);need(scan['status']=='PRELIMINARY_SOURCE_CLOSURE_SCAN_NOT_A_BUILD','scan status')
 rows=scan['modules'];need([x['module'] for x in rows]==['DiophantineConsistency.ArithmeticBinaryCarry','DiophantineConsistency.ArithmeticSaturation','DiophantineConsistency.ArithmeticRepunit','DiophantineConsistency.ArithmeticMaskPopulation'],'exact four modules')
 parent=json.loads((PARENT/'CHECK.json').read_bytes());need(sha(PARENT/'CHECK.json')=='922af1e2cb645f67b7ed102e1ad6bec809f297368891f6d19f4fb59a9570c27c' and parent['status']=='PASS_INDEPENDENT_FREEJ_POPULATION_CLIENT_AUDIT' and parent['recorded_outer_exit']==0,'parent audit')
 sources={}
 for loc in (BASE/'Lean/DiophantineConsistency',RESEARCH):
  for p in loc.rglob('*.lean'):sources.setdefault(p.stem,[]).append(p)
 lookup={x['module']:x for x in rows};leaf_counts={}
 for side in ('author','peer'):
  lib=PREFIX/side/'lib';obj={str(p.relative_to(lib)):p for p in lib.rglob('*.olean')};records=scan['inherited_objects'];need(len(obj)==len(records)==109 and set(obj)=={x['module_path'] for x in records},'provider inventory')
  for row in records:
   p=obj[row['module_path']];need(sha(p)==row['sha256'] and str(p.resolve())==row[side+'_resolved_path'],'provider hash '+row['module_path'])
  seen=set();order=[];leaves=set()
  def visit(n):
   if n in seen:return
   seen.add(n);rel=Path(*n.split('.')).with_suffix('.olean')
   if (lib/rel).is_file() or (PACKAGE/rel).is_file():leaves.add(n);return
   need(n in lookup,'unresolved '+n);row=lookup[n];opts=sources.get(n.split('.')[-1],[])
   need(len(opts)==1 and str(opts[0])==row['source'] and sha(opts[0])==row['source_sha256'],'source '+n)
   lines=opts[0].read_text().splitlines();need(not any(re.match(r'^\s+import\s',line) for line in lines),'indented import')
   imports=[x for line in lines if line.startswith('import ') for x in line[7:].split()];need(imports==row['imports'],'imports '+n)
   for dep in imports:visit(dep)
   order.append(n)
  for target in ('DiophantineConsistency.ArithmeticSaturation','DiophantineConsistency.ArithmeticMaskPopulation'):visit(target)
  need(order==[x['module'] for x in rows] and set(order)==set(lookup),'closure order/reachability')
  leaf_counts[side]=len(leaves)
 for p in files:
  name=p.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','e2ffe09c90:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(p),'post-check drift '+name)
 print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_SATURATION_SOURCE_CLOSURE_AUDIT','source_commit':'e2ffe09c90','normal_scan_exit':normal.returncode,'optimized_scan_exit':opt.returncode,'inherited_objects_per_side':109,'modules':[x['module'] for x in rows],'leaf_counts':leaf_counts,'scope':'Point-in-time source-declared closure and model-client draft only; no simultaneous freeze, compiled client, graph premise discharge, package/dynamic ancestry or PRA proof.'},indent=2))
if __name__=='__main__':main()
