import json,hashlib,re,math,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
root=Path(__file__).resolve().parents[4];base=root/'Computability/DiophantineConsistency';r=base/'research/ordinary12-ipra-bridge';p=r/'compact44-controller-closure-plan';result=json.loads((p/'scan.json').read_text());plan=json.loads((base/'research/thirteen-model-endpoint-closure/frontier-plan.json').read_text());survey=json.loads((base/'research/thirteen-model-endpoint-closure/source-manifest.json').read_text());historical=json.loads(Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json').read_text());rows=dict(historical['sources']);rows.update(survey['sources']);H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ('README.md','scan.py','scan.json','terminal-observation.json'):
 q=p/name;rel=q.relative_to(root).as_posix();blob=subprocess.run(['git','show','7af74cf65b:'+rel],cwd=root,capture_output=True,check=True).stdout;assert blob==q.read_bytes(),('committed bytes',name)
proc=subprocess.run([sys.executable,'-I','-S','-B',str(p/'scan.py')],capture_output=True,check=True,timeout=120);assert not proc.stderr and json.loads(proc.stdout)==result
assert H(base/'reviews/thirteen-model-endpoint-successor-pair-independent-audit/CHECK.json')=='50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce'
assert result['status']=='PRELIMINARY_COMPACT44_CONTROLLER_SOURCE_CLOSURE_NOT_A_BUILD'
for typ in ('Data','Choice'):
 data=result['modules'][typ];orig=base/'Lean/DiophantineConsistency'/('ArithmeticController'+typ+'.lean');cur=Path(data['source']);assert H(orig)==data['original_source_sha256'] and H(cur)==data['sha256']
 old=orig.read_text();new=cur.read_text();mapping=data['substitutions'];parts=re.split(r'(\b\w+\b)',old);converted=''.join(mapping.get(token,token) for token in parts)
 trailer='\n\n'+'\n'.join('#print axioms DiophantineConsistency.ArithmeticController'+typ+'Compact44.'+x for x in data['named_reports'])+'\n';assert new==converted.rstrip()+trailer
 assert [v for line in new.splitlines() if line.startswith('import ') for v in line[7:].split()]==data['imports']
projects={x['module']:x for x in result['source_declared_project_seed_modules']};external={x['module']:x for x in result['external_direct_or_transitive_leaves']};seen=set();ext=set();queue=result['modules']['Data']['imports']+result['modules']['Choice']['imports']
while queue:
 n=queue.pop()
 if n=='DiophantineConsistency.ArithmeticControllerDataCompact44':continue
 if n in seen or n in ext:continue
 if n not in rows:ext.add(n);continue
 seen.add(n);queue.extend(rows[n]['imports'])
assert seen==set(projects) and len(seen)==23 and seen<=set(plan['reusable_seeds']) and ext==set(external) and len(ext)==6
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');count=0
for n,row in projects.items():
 assert row['source_sha256']==rows[n]['sha256']==plan['all_selected_source_hashes'][n]==H(root/rows[n]['workspace_path'])
 for side in ('author','peer'):
  stem=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')/side/'lib'/Path(*n.split('.'));historic=Path('/tmp/ipra-aq29-fresh-project-pair')/side/'lib'/Path(*n.split('.'))
  for suffix in suffixes:
   p=Path(str(stem)+suffix);guard=plan['direct_and_seed_output_guards'][side][str(historic)+suffix];item=row[side][suffix]
   if p.is_file():assert item and guard and H(p)==item['sha256']==guard['sha256'] and str(p.resolve())==item['realpath']==guard['realpath']
   else:assert not p.is_symlink() and item is None and guard is None
   count+=1
  assert row[side]['.olean'] is not None
 assert {x:(y['sha256'] if y else None) for x,y in row['author'].items()}=={x:(y['sha256'] if y else None) for x,y in row['peer'].items()}
for n,row in external.items():
 for side in ('author','peer'):
  entry=plan['direct_external'][side][n];q=Path(entry['path']);assert q.is_file() and H(q)==entry['sha256']==row['companions']['.olean']['sha256']
for side in ('author','peer'):
 for typ in ('Data','Choice'):
  output=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01')/side/'lib/DiophantineConsistency'/('ArithmeticController'+typ+'Compact44.olean');assert not output.exists() and not output.is_symlink()
d=590069;p=581197;assert pow(2,d*(p-1),d*p*p)==172304811153038026==1+d*p*502425;assert 502425*134409%p==1;assert all(p%i for i in range(2,math.isqrt(p)+1))
choice=Path(result['modules']['Choice']['source']).read_text()
for t in ['theorem controller_choice','(hP2 :','(hs :','theorem rank_calibration','(hΓ :','(𝚺₁-Function₁ δ)']:assert t in choice
print(json.dumps({'status':'PASS_INDEPENDENT_CONTROLLER_SOURCE_CLOSURE','selected_modules':len(projects),'companion_slots_checked':count,'package_leaves':len(ext),'substitutions_checked':2,'finite_residue':172304811153038026,'scope':'Point-in-time historical seed and source substitution check; no parent audit rerun, Lean build, full package/dynamic ancestry, retained K/graph binding, machine or iPRA proof.'},indent=2))
