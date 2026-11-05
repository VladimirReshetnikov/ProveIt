#!/usr/bin/env python3
"""Recheck recorded historical/fresh source closure; no Lean execution."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
task=Path(__file__).resolve().parents[2];root=next(x for x in task.parents if (x/'lakefile.toml').is_file());p=task/'research/normalized106-historical-port-source-provenance';old=Path('/tmp/ha87-full-transitive-p3xt6wra');fresh=Path('/tmp/current14-standard-fresh-build-20261104');snap=Path('/tmp/current14-standard-fresh-source-20261104');stages=task/'reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'check.py':'29600f535c0e40823a21f22be5c696b59c718c2552e8e8fdd7450c2fba724f99',p/'result.json':'11096cdc8b7fb28074b53b1e64a275632eef4883de126b0d0f0bc991b73ebb7b',p/'outer-terminal.json':'ede299f578e43719e4e673307fd95b7626a05298b8e96e717f25746ec03234f3',old/'state.json':'84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90',fresh/'state.json':'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',snap/'manifest.json':'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',stages/'author/079/receipt.json':'33f040272cf2bc0203e21521ba20d5499bb6c39adc8de02e817a2e41b334318d',stages/'terminal.json':'6caef4771720124c2fd6612df8f76758ae68eef97211c129fde431f53ace84d8'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
def imports(text):
 i=0;depth=0;string=False;line=False;buf=[]
 while i<len(text):
  c=text[i];pair=text[i:i+2]
  if line:
   if c=='\n':line=False;buf.append('\n')
   i+=1;continue
  if depth:
   if pair=='/-':depth+=1;i+=2;continue
   if pair=='-/':depth-=1;i+=2;continue
   if c=='\n':buf.append('\n')
   i+=1;continue
  if string:
   if c=='\\':i+=2;continue
   if c=='"':string=False
   if c=='\n':buf.append('\n')
   i+=1;continue
  if pair=='--':line=True;i+=2;continue
  if pair=='/-':depth=1;buf.append(' ');i+=2;continue
  if c=='"':string=True;buf.append(' ');i+=1;continue
  buf.append(c);i+=1
 if depth or string:raise ValueError('unterminated source')
 result=[]
 for l in ''.join(buf).splitlines():
  m=re.match(r'^\s*(?:public\s+)?import\s+(.+)$',l)
  if m:result.extend(m.group(1).split())
 return result
O=json.loads((old/'state.json').read_bytes());F=json.loads((fresh/'state.json').read_bytes());M=json.loads((snap/'manifest.json').read_bytes());B=json.loads((p/'result.json').read_bytes());stage=json.loads((stages/'author/079/receipt.json').read_bytes());terminal=json.loads((stages/'terminal.json').read_bytes())
if O['status']!='PASS' or F['status']!='PASS' or F['source_status']!='CURRENT_AT_FINAL_CHECK' or F['manifest_sha256']!=sha(snap/'manifest.json') or stage['status']!='PASS' or terminal['exit_code']!=0:raise ValueError('producer statuses')
graph=O['graph']; seen=set();ext=set();todo=['DiophantineConsistency.CurrentKernelData2011']
while todo:
 n=todo.pop()
 if n in seen or n in ext:continue
 if n not in graph['sources']:ext.add(n);continue
 seen.add(n);todo.extend(graph['edges'][n])
if len(seen)!=12 or len(ext)!=8 or seen!={x['module'] for x in B['source_modules']} or ext!=set(B['external_imports']):raise ValueError('closure')
oldrecs={x['module']:x for x in O['records']};freshrecs={x['module']:x for x in F['records']};rows={x['module']:x for x in B['source_modules']}
for n in sorted(seen):
 oldsrc=old/'source-snapshots'/(n.replace('.','_')+'.lean');ms=M['sources'][n];newsrc=snap/ms['snapshot_path'];work=root/ms['workspace_path']
 if oldsrc.read_bytes()!=newsrc.read_bytes() or sha(oldsrc)!=graph['source_hashes'][n] or sha(newsrc)!=ms['sha256'] or sha(work)!=ms['sha256']:raise ValueError(('source',n))
 parsed=imports(newsrc.read_text())
 if parsed!=ms['imports'] or set(parsed)!=set(graph['edges'][n]):raise ValueError(('imports',n))
 oo=old/'lib'/(n.replace('.','/')+'.olean');fo=fresh/'lib'/(n.replace('.','/')+'.olean');oo_sha=sha(oo);fo_sha=sha(fo)
 if oldrecs[n]['exit']!=0 or freshrecs[n]['exit']!=0 or oo_sha!=oldrecs[n]['object_sha256'] or fo_sha!=freshrecs[n]['object_sha256'] or oo_sha==fo_sha:raise ValueError(('object',n))
 if rows[n]['source_sha256']!=sha(oldsrc) or rows[n]['old_object_sha256']!=oo_sha or rows[n]['fresh_object_sha256']!=fo_sha or rows[n]['objects_equal']:raise ValueError(('result row',n))
for n in ('DiophantineConsistency.CurrentKernelData2011','DiophantineConsistency.CurrentMaskData2011'):
 overlay=Path('/tmp/nine-ipra-guarded-author-20261102-h/lib')/(n.replace('.','/')+'.olean');original=old/'lib'/(n.replace('.','/')+'.olean')
 if overlay.resolve()!=original.resolve() or sha(overlay)!=sha(original):raise ValueError(('current overlay',n))
obj=Path(stage['output']['resolved'])
if stage['output']['sha256']!='79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122' or sha(obj)!=stage['output']['sha256']:raise ValueError('stage079 object')
run=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120)
if run.returncode!=0 or run.stderr or run.stdout!=(p/'result.json').read_bytes():raise ValueError(('author checker rerun',run.returncode,run.stderr[:200]))
outer=json.loads((p/'outer-terminal.json').read_bytes())
if outer['terminal_exit_code']!=0:raise ValueError('outer observation')
print(json.dumps({'status':'PASS_SOURCE_AND_OBJECT_PROVENANCE_RECHECK','project_modules':len(seen),'external_leaves':len(ext),'different_object_hashes':len(seen),'source_snapshots_byte_identical':True,'workspace_sources_match_now':True,'current_overlay_paths_checked':2,'checker_rerun_exit':run.returncode,'scope':'Recorded source closure and point-in-time object observations; not a dynamic load trace or actual numerical port theorem.'},sort_keys=True,indent=2))
