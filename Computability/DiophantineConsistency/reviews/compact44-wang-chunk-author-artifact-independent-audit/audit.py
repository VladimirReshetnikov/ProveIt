#!/usr/bin/env python3
"""Independent no-Lean audit of single-author Wang chunk artifacts."""
import hashlib,json,os,pathlib,re,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'): raise RuntimeError('isolated non-optimized Python required')
P=pathlib.Path;root=P.cwd();pkg=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-wang-table-chunk-explore';ev=pkg/'evidence-author';out=P('/tmp/ipra-wang-chunk-author-build-02');inv=P('/tmp/ipra-wang-chunk-author-inventory-02');seed=P('/tmp/ipra-graph-marked-explore-03/lib');package=P('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');lean=P('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();want='f79b98bb500a0cf2af5dfda7f7341468348bfc4f53664d6e15fb804902a23a3d';termhash='e410a3dbe56910b58913bdd4b4cc709f2baeca56aa2fe6418321d697a8a91343';invhash='b3ae1c41e5716e01412c4e76cf4a43b2208dc3885abb9d3aed624473800d57a9'
assert H(pkg/'replay.py')=='0c954807b7d8b75d299f4534a246c41fe541395b0d626a8a9a06ed9e512bd8e0' and H(pkg/'source-manifest.json')=='5c48ab43ebfbaada2798ee24e08fb277e350f8b1c434c5c78a404d84187103a4'
assert H(ev/'RESULT.json')==H(out/'RESULT.json')==want and H(ev/'terminal-observation.json')==termhash and H(ev/'inventory/observation.json')==H(inv/'observation.json')==invhash
term=json.loads((ev/'terminal-observation.json').read_bytes());result=json.loads((ev/'RESULT.json').read_bytes());pre=json.loads((ev/'preflight.json').read_bytes());manifest=json.loads((pkg/'source-manifest.json').read_bytes()); rows=manifest['sources'];steps=result['steps'];proof=[]
assert term['build']['actual_outer_exit']==0 and term['build']['session_id']==63717 and term['build']['result_sha256']==want and term['build']['children']==96 and term['build']['reports']==94
assert term['final_inventory']['session_id']==68387 and term['final_inventory']['actual_outer_exit']==0 and term['final_inventory']['observation_sha256']==invhash and term['final_inventory']['reports']==29 and term['no_lean_process_after_inventory'] is True
assert term['separate_preflight']['actual_outer_exit']==0 and H(ev/'separate-preflight/preflight.json')==term['separate_preflight']['preflight_sha256'] and (ev/'separate-preflight/wrapper.stderr').stat().st_size==0
assert result['status']=='PASS_AUTHOR_ONLY_CHUNKED_TABLE' and len(rows)==len(steps)==pre['source_count']==96 and len(result['final_direct_and_output_slots'])==1970
assert (ev/'wrapper.stderr').stat().st_size==0 and (ev/'inventory/wrapper.stderr').stat().st_size==0
for n in ('preflight.json','progress.json'):
 assert H(ev/n)==H(out/n)
progress=json.loads((ev/'progress.json').read_bytes());assert progress['steps']==steps
stdout=(ev/'wrapper.stdout').read_text().splitlines();assert len(stdout)==98 and stdout[-1]=='PASS_AUTHOR_ONLY_CHUNKED_TABLE';assert json.loads(stdout[0])['status']=='READY_AUTHOR_ONLY_NO_LEAN'
for step,line in zip(steps,stdout[1:-1]):
 before={k:v for k,v in step.items() if k not in ('output_slots','axiom_reports')};assert json.loads(line)==before
assert len(list((ev/'logs').glob('*.log')))==96
pat=re.compile(r"(?m)^'([^']+)' (?:(?:depends on axioms:\s*\[([^\]]*)\])|(does not depend on any axioms))")
def reports(source,text):
 names=re.findall(r'^#print\s+axioms\s+([\w.]+)\s*$',source,re.M);ms=list(pat.finditer(text)); d={}
 for m in ms:
  n=m.group(1);assert n not in d
  vals=[] if m.group(3) else [x.strip() for x in m.group(2).split(',') if x.strip()];assert len(vals)==len(set(vals)) and set(vals)<={'propext','Classical.choice','Quot.sound'} and (m.group(3) or vals);d[n]=vals
 assert len(names)==len(set(names)) and set(names)==set(d) and not pat.sub('',text).strip();return d
allowed=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def checkslots(dic):
 for name,record in dic.items():
  p=P(name)
  if record is None:assert not os.path.lexists(p),name
  else:assert p.is_file() and str(p.resolve(strict=True))==record['realpath'] and H(p)==record['sha256'],name
checkslots(result['final_direct_and_output_slots'])
assert len(pre['direct_companion_slots'])==1010 and len(pre['source_pins'])==96
names=[r['module'] for r in rows];assert len(set(names))==96 and [s['module'] for s in steps]==names
original=root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticWangTable.lean'; original_text=original.read_text();assert H(original)==manifest['original_table_source_sha256']=='8bf620443a3ed74892efba1aeaa6f8c14add5feaff4954dda001a6acf5e36ff2'
base=(pkg/'sources/ArithmeticWangTableChunkBase.lean').read_text().rstrip().removesuffix('end DiophantineConsistency.ArithmeticWangTable').rstrip();assert base==original_text[:original_text.index('theorem rows_goodA :')].rstrip()
last=(pkg/'sources/ArithmeticWangTable.lean').read_text();assert last[last.index('theorem tileN_mem'):]==original_text[original_text.index('theorem tileN_mem'):]
for pred in 'ABC':
 agg=(pkg/f'sources/ArithmeticWangTableChunk{pred}All.lean').read_text();assert re.findall(r'^import (.*)',agg,re.M)==['DiophantineConsistency.ArithmeticWangTableChunkCover']+[f'DiophantineConsistency.ArithmeticWangTableChunk{pred}{k:02}' for k in range(30)]
 for k in range(30):
  c=(pkg/f'sources/ArithmeticWangTableChunk{pred}{k:02}.lean').read_text();part=f'(orderedRows.drop {32*k}).take 32' if k<29 else 'orderedRows.drop 928';assert f'theorem rows_good{pred}_chunk{k:02} : ∀ row ∈ {part}, Good{pred} row.2 := by decide +kernel' in c
  if k<29:assert f'have h{k} : ∀ row ∈ orderedRows.drop {32*k}, Good{pred} row.2 := by' in agg and f'apply chunk_cover (fun row => Good{pred} row.2) (orderedRows.drop {32*k}) 32' in agg and f'exact rows_good{pred}_chunk{k:02}' in agg and f'using h{k+1}' in agg
  else:assert f'have h29 : ∀ row ∈ orderedRows.drop 928, Good{pred} row.2 := rows_good{pred}_chunk29' in agg
 assert 'simpa only [List.drop_zero] using h0' in agg
outputs={};allreports={}
for pos,(row,step) in enumerate(zip(rows,steps),1):
 name=row['module'];src=pkg/row['source'];frozen=(out/'frozen'/P(*name.split('.'))).with_suffix('.lean');obj=(out/'lib'/P(*name.split('.'))).with_suffix('.olean');log=out/(str(pos).zfill(3)+'-'+name.replace('.','_')+'.log');saved=ev/'logs'/log.name
 assert src.is_file() and not src.is_symlink() and H(src)==H(frozen)==row['sha256'] and pre['source_pins'][str(frozen)]==row['sha256'] and not frozen.is_symlink()
 assert step['position']==pos and type(step['compiler_exit']) is int and step['compiler_exit']==0 and step['reason'] is None and type(step['peak_sampled_rss_bytes']) is int and 0<step['peak_sampled_rss_bytes']<=int(3.5*1024**3)
 assert step['compiler_command']==[str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(out/'frozen'),str(frozen),'-o',str(obj)] and step['deps_command']==[str(lean),'--deps',str(frozen)]
 assert log.is_file() and saved.is_file() and H(log)==H(saved)==step['log_sha256'] and not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',log.read_text())
 rr=reports(frozen.read_text(),log.read_text());assert rr==step['axiom_reports'];allreports.update(rr)
 snap=step['output_slots'];assert len(snap)==10 and obj.is_file() and not obj.is_symlink() and snap[str(obj)] is not None;assert all(v is None for k,v in snap.items() if k!=str(obj));checkslots(snap)
 assert set(snap)=={str(P(str(obj)[:-6]+suffix)) for suffix in allowed}
 mapping=pre['direct_inputs'][name];expected=set()
 imports=re.findall(r'^import\s+([\w.]+)',frozen.read_text(),re.M);assert set(mapping)==set(['Init']+imports)
 for dep,item in mapping.items():
  rel=P(*dep.split('.')).with_suffix('.olean');candidates=[out/'lib'/rel,package/rel];first=next((p for p in candidates if p.is_file()),None);chosen=P(item['path']);assert first==chosen
  if item['kind']=='static':assert item['record']==result['final_direct_and_output_slots'][str(chosen)]
  else:assert item['kind']=='produced' and dep in outputs and result['final_direct_and_output_slots'][str(chosen)]==outputs[dep]
  expected.add(str(chosen.resolve()))
 assert {str(P(x).resolve()) for x in step['deps_stdout'].splitlines() if x.strip()}==expected
 outputs[name]=snap[str(obj)];proof.append({'module':name,'source_sha256':row['sha256'],'object_sha256':H(obj),'log_sha256':H(log),'reports':rr})
assert len(allreports)==94 and max(x['peak_sampled_rss_bytes'] for x in steps)==term['build']['peak_sampled_leader_rss_bytes']
assert {k for k,v in allreports.items() if set(v)!={'propext','Classical.choice','Quot.sound'}}=={'DiophantineConsistency.ArithmeticWangTable.chunk_cover'}
assert allreports['DiophantineConsistency.ArithmeticWangTable.chunk_cover']==['propext']
checkslots(pre['direct_companion_slots'])
def files(p):
 f={};links=[]
 for d,dirs,fs in os.walk(p,followlinks=False):
  for x in dirs:
   if P(d,x).is_symlink():links.append(str(P(d,x)))
  for x in fs:f[P(d,x).relative_to(p).as_posix()]=P(d,x)
 assert not links
 return f
seedfiles=files(seed);actual=files(out/'lib');new={str(P(*n.split('.')).with_suffix('.olean')) for n in names};assert len(seedfiles)==425 and len(actual)==521 and not(set(seedfiles)&new) and set(actual)==set(seedfiles)|new
for name,p in seedfiles.items():
 q=actual[name];assert q.is_symlink() and str(q.resolve())==str(p.resolve()) and H(q)==H(p)
i=json.loads((ev/'inventory/observation.json').read_bytes());assert i['status']=='PASS_AUTHOR_ONLY_FINAL_AXIOM_INVENTORY' and i['compiler_exit']==0 and i['reason'] is None and i['build_receipt_sha256']==want
client=pkg/'follow-up/FinalWangTableInventory.lean';frozen=inv/'frozen/FinalWangTableInventory.lean';assert H(client)==H(frozen)==H(ev/'inventory/FinalWangTableInventory.lean')==i['source_sha256'] and not frozen.is_symlink()
log=inv/'compiler.log';assert H(log)==H(ev/'inventory/compiler.log')==i['compiler_log_sha256'] and not re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',log.read_text());r=reports(client.read_text(),log.read_text());assert r==i['reports'] and len(r)==29
obj=inv/'FinalWangTableInventory.olean';table=out/'lib/DiophantineConsistency/ArithmeticWangTable.olean';assert H(table)==i['table_sha256']==outputs['DiophantineConsistency.ArithmeticWangTable']['sha256'];checkslots(i['direct_slots']);checkslots(i['output_slots']);assert obj.is_file() and not obj.is_symlink() and H(obj)==i['output_slots'][str(obj)]['sha256']
assert i['command']==[str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(inv/'frozen'),str(frozen),'-o',str(obj)] and i['deps_command']==[str(lean),'--deps',str(frozen)] and {str(P(x).resolve()) for x in i['deps_stdout'].splitlines() if x.strip()}=={str((package/'Init.olean').resolve()),str(table.resolve())}
assert {k for k,v in r.items() if set(v)!={'propext','Classical.choice','Quot.sound'}}=={'DiophantineConsistency.ArithmeticWangTable.lookup_eq_actCode'}
assert set(r['DiophantineConsistency.ArithmeticWangTable.lookup_eq_actCode'])=={'propext','Quot.sound'}
transcripts=[(ev/'wrapper.stdout',P('/tmp/ipra-wang-chunk-author-build-02.stdout')),(ev/'wrapper.stderr',P('/tmp/ipra-wang-chunk-author-build-02.stderr')),(ev/'separate-preflight/preflight.json',P('/tmp/ipra-wang-chunk-author-preflight-02/preflight.json')),(ev/'separate-preflight/wrapper.stdout',P('/tmp/ipra-wang-chunk-author-preflight-02.stdout')),(ev/'separate-preflight/wrapper.stderr',P('/tmp/ipra-wang-chunk-author-preflight-02.stderr')),(ev/'inventory/wrapper.stdout',P('/tmp/ipra-wang-chunk-author-inventory-02.stdout')),(ev/'inventory/wrapper.stderr',P('/tmp/ipra-wang-chunk-author-inventory-02.stderr')),(ev/'inventory/run.py',P('/tmp/compact44-wang-final-inventory-run.py'))]
assert all(a.read_bytes()==b.read_bytes() for a,b in transcripts)
sp=json.loads((ev/'separate-preflight/wrapper.stdout').read_text());assert sp['status']=='READY_AUTHOR_ONLY_NO_LEAN' and sp['sources']==96 and sp['direct_slots']==1010
output=json.loads((ev/'inventory/wrapper.stdout').read_text());assert output['observation_sha256']==invhash and output['status']==i['status'] and output['reports']==29 and output['compiler_exit']==0
print(json.dumps({'status':'PASS_INDEPENDENT_AUTHOR_ONLY_WANG_ARTIFACT_AUDIT','evidence_commit':'eebdd9046b','result_sha256':want,'terminal_sha256':termhash,'inventory_observation_sha256':invhash,'source_modules':96,'source_assembly':'A/B/C each 29 full 32-row slices and full drop-928 tail; original prefix and suffix match','source_rows':proof,'named_reports':len(allreports),'report_axiom_sets':{k:v for k,v in allreports.items()},'inherited_objects':len(seedfiles),'overlay_objects':len(actual),'guard_slots':len(result['final_direct_and_output_slots']),'inventory_reports':r,'inventory_report_count':len(r),'lean_launched':False,'scope':'Single-author artifact verification; inherited seed/package transitive ancestry remains unauthenticated, not a paired replay or PRA proof.'},indent=2,sort_keys=True))
