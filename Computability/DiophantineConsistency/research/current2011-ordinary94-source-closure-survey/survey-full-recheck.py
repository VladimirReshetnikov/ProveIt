#!/usr/bin/env python3
"""Source-declared ModelCarrier94 vs compact local bridge survey; no Lean."""
import contextlib,hashlib,io,json,os,runpy,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
HERE=Path(__file__).resolve().parent;D=HERE.parents[1];ROOT=next(p for p in HERE.parents if (p/'lakefile.toml').is_file());R=HERE.parent
scan=R/'nine-variable-ipra/bounded-build-preflight/scan.py';basepath=R/'current14-standard-fresh-rebuild-preflight/snapshot-manifest.json';fp=R/'normalized106-current14-sixteen-source-preflight/result.json';audit=D/'reviews/normalized106-fresh-base-model-independent/check.py';base=Path('/tmp/current14-standard-fresh-build-20261104/lib');overlay=Path('/tmp/normalized106-fresh-model-build-v2-20261105/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');tool=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');client=Path('/tmp/normalized106-fresh-model-client-20261105/FreshModel106.olean')
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={scan:'d72f3242ff991ad537217b8b25c3cde4ab091a06ce45f61d4f92f70886848816',basepath:'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',fp:'f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2',audit:'2f1e8f23caabe818d51ec8f3c56f6752794c9dee755624794cc8fb154a77361f',client:'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942',ROOT/'lakefile.toml':'a378413000dd01d021315457d6c569202cca123f99dd224774e951fef3ec9b4f'}
def pincheck():
 for p,h in pins.items():need(p.is_file() and H(p)==h,'pin '+str(p))
pincheck();b=json.loads(basepath.read_text());f=json.loads(fp.read_text());run=subprocess.run([sys.executable,'-I','-S','-B',str(audit)],capture_output=True);need(run.returncode==0 and run.stdout==(audit.parent/'result.json').read_bytes(),'prior provider audit')
with contextlib.redirect_stdout(io.StringIO()):scanmod=runpy.run_path(str(scan))
def collect(targets):
 all={};ext=set()
 for t in targets:
  seen,missing,external=scanmod['graph'](t);need(not missing,'missing '+repr(missing));ext.update(external)
  for n,v in seen.items():need(n not in all or all[n]==v,'disagree source '+n);all[n]=v
 return all,ext
full,full_external=collect(['DiophantineConsistency.ModelCarrier94']);small,small_external=collect(['DiophantineConsistency.Carrier94Value','DiophantineConsistency.ArithmeticCarrier94Extraction'])
base_names=set(b['sources']);ext16=set(f['extension_order']);available=base_names|ext16
need(len(base_names)==1000 and len(ext16)==16 and not (base_names&ext16),'provider module inventories');need((len(full),len(set(full)&base_names),len(set(full)&ext16),len(set(full)-available))==(1144,995,16,133),'unexpected full closure')
extra=set(small)-available;expected={'DiophantineConsistency.Carrier94Value','DiophantineConsistency.Carrier94Syntax','DiophantineConsistency.ArithmeticCarrier94Extraction','DiophantineConsistency.ArithmeticCarrier94Indices','DiophantineConsistency.ArithmeticCarrier94Soundness','DiophantineConsistency.ArithmeticPellResidueAux'};need(extra==expected,'unexpected compact closure '+repr(sorted(extra)))
for name,rec in small.items():
 need(H(ROOT/rec['source'])==rec['source_sha256'],'current source drift '+name)
 if name in base_names:need(rec['source_sha256']==b['sources'][name]['sha256'] and rec['imports']==b['sources'][name]['imports'],'base source drift '+name)
 if name in ext16:need(rec['source_sha256']==f['project_sources'][name]['source_sha256'] and rec['imports']==f['project_sources'][name]['imports'],'extension source drift '+name)
for name,rec in full.items():
 need(H(ROOT/rec['source'])==rec['source_sha256'],'full source drift '+name)
 if name in base_names:need(rec['source_sha256']==b['sources'][name]['sha256'] and rec['imports']==b['sources'][name]['imports'],'full base source drift '+name)
 if name in ext16:need(rec['source_sha256']==f['project_sources'][name]['source_sha256'] and rec['imports']==f['project_sources'][name]['imports'],'full extension source drift '+name)
active=set();done=set();order=[]
def visit(n):
 if n in done:return
 need(n not in active,'cycle '+n);active.add(n)
 for x in small[n]['imports']:
  if x in small:visit(x)
 active.remove(n);done.add(n)
 if n in extra:order.append(n)
for t in ('DiophantineConsistency.Carrier94Value','DiophantineConsistency.ArithmeticCarrier94Extraction'):visit(t)
need(set(order)==extra and len(order)==6,'incomplete order');external_base=set(b['external_modules'])|set(f['declared_external']);new=sorted(small_external-external_base);need(not new,'new external names '+repr(new))
roots=[overlay,pkg,tool];suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash'];absences={}
for n in order:
 stem=Path(*n.split('.'));obs={}
 for root in roots:
  for ext in suffixes:
   p=root/(str(stem)+ext);need(not os.path.lexists(p),'existing provider or shadow '+str(p));obs[str(p)]=None
 absences[n]=obs
pincheck();result={'status':'PASS_SOURCE_SURVEY_NOT_BUILD','full_target':'DiophantineConsistency.ModelCarrier94','full_project_count':len(full),'full_shared_base':len(set(full)&base_names),'full_shared_extension':len(set(full)&ext16),'full_additional_count':len(set(full)-available),'full_additional':sorted(set(full)-available),'minimal_provider_targets':['DiophantineConsistency.Carrier94Value','DiophantineConsistency.ArithmeticCarrier94Extraction'],'minimal_project_count':len(small),'minimal_base_count':len(set(small)&base_names),'minimal_existing_16_count':len(set(small)&ext16),'minimal_extra_count':len(order),'minimal_extra_order':order,'minimal_extra_sources':{n:small[n] for n in order},'minimal_external':sorted(small_external),'new_external_module_names_relative_to_base_and_106':new,'extra_provider_absences':absences,'source_and_provider_pins':{str(p):h for p,h in pins.items()},'scope':'Source-declared closure and point-in-time direct candidates only. Inline no-zero bridge and locally adapt ModelCarrier94 using FreshModel106; no Lean build, immutable snapshot, dynamic load trace, package-transitive compatibility, or reverse theorem asserted.'}
print(json.dumps(result,indent=2,sort_keys=True))
