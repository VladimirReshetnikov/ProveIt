#!/usr/bin/env python3
"""Stage existing ten routing245 coverage pilot proofs and lossless UTF8 history.
No compiler, checker, simulation, source regeneration, maintained writes or Git.
The three subtree objects are later production dependencies; seven leaf checks
are measurements. Neither family is a complete all-sites proof.
"""
from pathlib import Path
import argparse,base64,hashlib,json,re,shutil,zlib
B=Path('/tmp/zfc-routing245-lean')
ROOTS={'leaf':B/'coverage-pilots','subtree':B/'coverage-subtree-pilots'}
RECORDS={
 'leaf1704':('leaf','leaf1704-run1/case1704/verification.json','659ccf67b43f136e932125ad6f7ed5d1b3575d0769b94e0c95d64347ed0d8bc4'),
 'leaf1609':('leaf','remaining6-run1/case1609/verification.json','d8bd5d4d7370775bf551e6b83df431a241cb40b1232ad0d4f410a0bbe06eeaef'),
 'leaf1703':('leaf','remaining6-run1/case1703/verification.json','d84d26084cbca551d76879fb2b78cd4f7e929f66d82b46286017233c22286754'),
 'leaf1705':('leaf','remaining6-run1/case1705/verification.json','34b6b8dad30049e3f9e64041d5d10c047b0b6edbb53b68167d922828d4d8f3e3'),
 'leaf1720':('leaf','remaining6-run1/case1720/verification.json','04ea0f1c77a7fadd68da7dacbe51f66ac7ea031b6a6b23b7759a370f3d6a1a31'),
 'leaf4730':('leaf','remaining6-run1/case4730/verification.json','213e05ec06e16897ad057ba226da73ea7b1d83cea5566f1110da7b0952ca91bd'),
 'leaf6324':('leaf','remaining6-run1/case6324/verification.json','9268d0eda586582171321e3d314cfae0a1c060caf99ef18ae06bccf4b25af81c'),
 'cut070':('subtree','cut070-run1/cut070/verification.json','f69992ea47733e19e84e8c1d25c16200ebd261329e8de4bea2634359074408eb'),
 'cut000':('subtree','remaining2-run1/cut000/verification.json','d343f1c8b0618bf19b46bd5140da920f757e1e9550b1bf2cd75f84811edcceb1'),
 'cut174':('subtree','remaining2-run1/cut174/verification.json','30ddc599a0511ca665e6258cdd245787dcc3ae1d2b348b6b8ab83b778b35e5d2')}
Q='Computability/BusyBeaver/Research/ZFC'
L='Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
DEST=Q+'/routing245-coverage-pilots'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise RuntimeError(m)
def descriptor(p):return dict(path=str(p),sha256=sha(p),bytes=Path(p).stat().st_size)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
 out=args.output.resolve();repo=Path('/home/codex/.codex/worktrees/ec20/Proofs').resolve()
 need(not out.exists() and not out.is_relative_to(repo) and all(not out.is_relative_to(p) for p in ROOTS.values()),'New external output outside archive roots required.')
 units=[];seen=set();probes=0;callers=0
 for key,(family,relative,pin) in RECORDS.items():
  path=ROOTS[family]/relative;need(sha(path)==pin,'Changed actual record '+key);d=json.loads(path.read_text())
  need(d['status']=='PASS' and not d['prepare_only'] and d['before']==d['after'] and
       d['only_standard_axioms'] and d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit'] and
       d['source_object_recorded_before_audit'],'Incomplete actual '+key)
  need([c['label'] for c in d['commands']]==['source','audit'] and all(c['exit_code']==0 and not c.get('timed_out',False) for c in d['commands']),'Failed command '+key)
  need(d['warnings']==dict(source=0,audit=0),'Unexpected warning '+key)
  for p,h in d['before'].items():need(sha(p)==h,'Current input changed '+p)
  for role in ['source','audit']:
   need(sha(d[role]['path'])==sha(d[role]['snapshot'])==d[role]['sha256'],'Snapshot changed '+key)
  fresh=d['fresh_modules'];need(len(fresh)==1,'Fresh object census');f=fresh[0]
  need(f['module'] not in seen,'Repeated module');seen.add(f['module'])
  need(sha(f['path'])==f['sha256'] and f['source_sha256']==d['source']['sha256'],'Fresh source binding changed')
  need(all(d['source_pass_object'][k]==f[k] for k in ['module','path','sha256','source_sha256']),'Pre-audit binding')
  need(len(re.findall(r'^#print axioms ',Path(d['audit']['path']).read_text(),re.M))==d['named_axiom_probes'] and
       len(re.findall(r'^example\b',Path(d['audit']['path']).read_text(),re.M))==d['callers'],'Audit census')
  for c in d['commands']:
   log=path.parent/(c['label']+'.log');need(log.read_text()==c['output'],'Raw log differs '+key)
  units.append(dict(key=key,family=family,module=f['module'],record=descriptor(path),source=d['source'],audit=d['audit'],fresh_object=f,
                    probes=d['named_axiom_probes'],callers=d['callers'],seconds={c['label']:c['seconds'] for c in d['commands']}))
  probes+=d['named_axiom_probes'];callers+=d['callers']
 need((len(units),probes,callers)==(10,17,31),'Ten-module17/31 census')
 # Every UTF8 path is archived byte-for-byte; compiled cache products and links
 # are listed explicitly as exclusions instead of silently omitted.
 blobs={};aliases=[];excluded=[]
 for family,root in ROOTS.items():
  for p in sorted(root.rglob('*')):
   if p.is_dir():continue
   relative=str(p.relative_to(root));logical=family+'/'+relative
   if p.is_symlink() or 'cache' in p.relative_to(root).parts or p.suffix in {'.olean','.ilean','.c','.o','.pyc','.a','.so'}:
    excluded.append(dict(path=logical,reason='compiled_cache_or_symlink',target=str(p.resolve()) if p.is_symlink() else None));continue
   data=p.read_bytes()
   try:data.decode('utf-8')
   except UnicodeDecodeError:raise RuntimeError('Unexpected non-UTF8 noncache input '+str(p))
   digest=hashlib.sha256(data).hexdigest();blobs.setdefault(digest,base64.b64encode(zlib.compress(data,9)).decode('ascii'))
   aliases.append(dict(path=logical,original=str(p),sha256=digest,bytes=len(data)))
 for row in aliases:
  recovered=zlib.decompress(base64.b64decode(blobs[row['sha256']]));need(recovered==Path(row['original']).read_bytes(),'Archive roundtrip '+row['path'])
 out.mkdir();files=out/'files';mapping=[];destinations=set()
 def put(data,dest,origin=None):
  need(dest not in destinations,'Duplicate destination '+dest);destinations.add(dest)
  p=files/dest;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
  mapping.append(dict(source=str(p),destination=dest,sha256=sha(p),bytes=len(data),origin=origin))
 for u in units:
  stem=u['module'].split('.')[-1];recordpath=Path(u['record']['path'])
  put(Path(u['source']['path']).read_bytes(),L+'/'+stem+'.lean',u['source']['path'])
  put(Path(u['audit']['path']).read_bytes(),DEST+'/audits/'+stem+'.lean',u['audit']['path'])
  put(recordpath.read_bytes(),Q+'/results/routing245-coverage-pilot-'+u['key']+'-verification.json',str(recordpath))
  for label in ['source','audit']:
   p=recordpath.parent/(label+'.log');put(p.read_bytes(),DEST+'/logs/'+u['key']+'-'+label+'.log',str(p))
 # Original execution programs are provenance; no speculative portable guard.
 for family,root in ROOTS.items():
  for p in sorted(root.iterdir()):
   if p.is_file() and not p.is_symlink():put(p.read_bytes(),DEST+'/provenance/'+family+'/'+p.name,str(p))
 history=dict(format='lossless-utf8-zlib-base64-by-sha256',scope='All noncache original pilot files including preparations, runs, snapshots, generators, guards and reviews.',
              roots={k:str(v) for k,v in ROOTS.items()},aliases=aliases,blobs=blobs,excluded=excluded,roundtrip_verified=True)
 put((json.dumps(history,indent=2)+'\n').encode(),DEST+'/history.json')
 publication=dict(status='EXISTING_PASS_PACKET',scope='Seven individual leaves and three actual-tree subtrees; no complete all-sites or binary/PA endpoint.',
  units=units,named_axiom_probes=probes,typed_callers=callers,warnings=0,
  coverage=dict(leaf_family_leaves=7,leaf_family_guard_cases=9,subtree_family_leaves=90,subtree_family_guard_cases=117,
                note='Families overlap; do not add these coverage counts. Production reuses three subtree objects separately.'),
  history_paths=len(aliases),history_unique_blobs=len(blobs),compiled_exclusions=len(excluded),history_roundtrip_verified=True,
  builder=descriptor(Path(__file__)),no_compiler_or_checker_execution=True,no_portable_guard_claim=True)
 put((json.dumps(publication,indent=2)+'\n').encode(),DEST+'/publication.json')
 (out/'map.json').write_text(json.dumps(dict(files=mapping),indent=2)+'\n')
 print(json.dumps(dict(map=descriptor(out/'map.json'),files=len(mapping),history_paths=len(aliases),unique_blobs=len(blobs),excluded=len(excluded)),indent=2))
if __name__=='__main__':main()
