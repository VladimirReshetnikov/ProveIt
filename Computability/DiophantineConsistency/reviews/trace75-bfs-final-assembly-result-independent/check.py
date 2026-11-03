from pathlib import Path
import hashlib,json,os,re
root=Path(__file__).resolve().parents[2];H=root/'research/trace75-bfs-ipra-final-assembly-plan';a=H/'observations/attempt01';o=H/'observations/outer-attempt01';r=json.loads((a/'result.json').read_text());outer=json.loads((o/'terminal.json').read_text());plan=json.loads((H/'plan.json').read_text());parentdir=root/'research/trace75-bfs-compatible-forward-rebuild/observations/attempt01';parent=json.loads((parentdir/'result.json').read_text());bfs=json.loads((root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text());extra=json.loads((root/'research/trace75-bfs-compatible-reverse-plan/observations/outside-attempt01/result.json').read_text());outside=json.loads((root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'result.json')=='b05b0970cde855c6c65973b9550ae7231b7cca02f8659140a166f206bf51093c' and sha(o/'terminal.json')=='2188db777c5fe442be871c30d29943de70fe0c1d20325d49b00bb9886e56c69d'
assert r['status']=='PASS' and outer['exit']==0 and outer['child_status']=='PASS' and outer['child_result_sha256']==sha(a/'result.json') and outer['inputs_before']==outer['inputs_after'] and outer['wrapper_sha256_before']==outer['wrapper_sha256_after']==sha(H/'run-outer.py')
for n in ('stdout','stderr'):assert sha(o/n)==outer[n+'_sha256']
for p,d in {**r['inputs'],**outer['inputs_before']}.items():assert sha(p)==d,p
assert sha(H/'run.py')==r['runner_sha256'] and sha(a/'initial-union.json')==r['initial_union_sha256']
base=json.loads((a/'initial-union.json').read_text());assert len(base)==2011 and r['stage_order']==[p['module'] for p in plan['stages']] and len(r['stages'])==5
parentbase=json.loads((parentdir/'initial-union.json').read_text())
for s in parent['stages']:assert s['module'] not in parentbase;parentbase[s['module']]=s['object']
def hashes(bundle):return {s:(None if v is None else v['sha256']) for s,v in bundle.items()}
assert set(base)==set(parentbase)
for n in base:assert hashes(base[n])==hashes(parentbase[n]),n
lib=Path(r['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
names=[['DiophantineConsistency.TenPositiveTrace75.evalRing_expression'],['Trace75BFSSyntax.literal_zero_iff'],['Trace75BFSModelIff.positive_model_iff'],['Trace75BFSIPRA.'+x for x in ['positive_bridge','native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']],['Trace75BFSFixedIPRA.'+x for x in ['native_consistency','standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency']]]
for i,(s,p) in enumerate(zip(r['stages'],plan['stages']),1):
 n=s['module'];assert s['index']==i and n==p['module'] and s['status']=='PASS' and s['exit']==0 and s['reason'] is None and n not in base
 assert sha(s['source'])==sha(a/f'stage-{i:02}.source.lean')==s['source_sha256']==p['sha256'];out=a/f'stage-{i:02}.stdout';err=a/f'stage-{i:02}.stderr';assert sha(out)==s['stdout_sha256'] and sha(err)==s['stderr_sha256'] and not err.read_bytes()
 expected=''.join("'"+name+"' depends on axioms: "+('[propext]' if i==1 else '[propext, Classical.choice, Quot.sound]')+'\n' for name in names[i-1]);assert out.read_text()==expected
 assert s['direct_imports']==s['direct_imports_after'] and set(s['direct_imports'])==set(p['imports'])
 for dep,b in s['direct_imports'].items():
  candidates=[q/(dep.replace('.','/')+'.olean') for q in (lib,pack,core) if os.path.lexists(q/(dep.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and sha(candidates[0])==b['.olean']['sha256'] and str(candidates[0].resolve(strict=True))==b['.olean']['resolved']
  for suffix,v in b.items():
   q=Path(str(candidates[0])[:-6]+suffix)
   if v is None:assert not os.path.lexists(q)
   else:assert q.is_file() and str(q.resolve(strict=True))==v['resolved'] and sha(q)==v['sha256']
 assert s['object']['.olean'] and sha(s['object']['.olean']['path'])==s['object']['.olean']['sha256'];base[n]=s['object']
 for snap in [s['preflight'],s['postflight'],*s['samples']]:assert snap['mem_available_kib']>=8*1024**2 and len(snap['lean'])<=2
assert len(base)==r['union_count']==2016
actual={str(x.relative_to(lib)) for x in lib.rglob('*') if x.is_file() or x.is_symlink()};want={n.replace('.','/')+suffix for n,b in base.items() for suffix,v in b.items() if v is not None};assert actual==want
for n,bundle in base.items():
 for suffix,v in bundle.items():
  p=lib/(n.replace('.','/')+suffix)
  if v is None:assert not os.path.lexists(p)
  else:assert p.is_file() and str(p.resolve(strict=True))==v['resolved'] and sha(p)==v['sha256']
heads=r['serialized_headers'];assert set(heads)==set(r['selected_project']) and len(heads)==1868 and len(r['selected_outside'])==81
def closure(n,g):
 pending=[n];ins=set();out=set()
 while pending:
  x=pending.pop()
  if x in ins or x in out:continue
  if x not in g:out.add(x);continue
  ins.add(x);pending.extend(g[x])
 return {'project':sorted(ins),'outside':sorted(out)}
prior=bfs['closure']['project'];bg={n:x['imports'] for n,x in prior.items()}
for n in r['closures']:
 assert closure(n,heads)==r['closures'][n]
 if n in ('DirectBFSBandCarry','DirectBFSHaltPellSeed'):
  assert closure(n,bg)==r['closures'][n]==parent['closures'][n]
  for dep in r['closures'][n]['project']:assert dep in prior and hashes(r['selected_project'][dep])==hashes(prior[dep]['companions']),dep
 if n in ('Trace75BFSHaltGraph','Trace75BFSModelHalt'):
  assert r['closures'][n]==parent['closures'][n]
  for dep in r['closures'][n]['project']:assert hashes(r['selected_project'][dep])==hashes(parent['selected_project'][dep]),dep
  for dep in r['closures'][n]['outside']:assert hashes(r['selected_outside'][dep])==hashes(parent['selected_outside'][dep]),dep
for n in r['header_reuse']:
 h=r['selected_project'][n]['.olean']['sha256'];cached=parent['selected_project'].get(n);old=prior.get(n)
 if cached is not None and cached['.olean']['sha256']==h:assert heads[n]==parent['serialized_headers'][n]
 else:assert old is not None and old['record']['sha256']==h and heads[n]==old['imports']
for i,row in enumerate(r['headers']):
 assert row['status']=='PASS' and row['exit']==0 and row['reason'] is None;out=a/f'header-{i:03}.stdout';err=a/f'header-{i:03}.stderr';assert sha(out)==row['stdout_sha256'] and sha(err)==row['stderr_sha256'] and not err.read_bytes();current=None;parsed={}
 for line in out.read_text().splitlines():
  if line.startswith('BEGIN '):current=Path(line[6:]).relative_to(lib).as_posix()[:-6].replace('/','.');assert current not in parsed;parsed[current]=[]
  elif line.startswith('IMPORT ') and current is not None:parsed[current].append(line[7:])
  elif line=='END' and current is not None:current=None
  else:raise AssertionError(line)
 assert current is None
 for n,imports in parsed.items():assert heads[n]==imports
for p in plan['stages']:assert 'Init' in heads[p['module']] and [x for x in heads[p['module']] if x!='Init']==p['imports']
assert extra['module'] not in outside;outside[extra['module']]=extra['record'];assert len(outside)==81
for n,b in outside.items():
 candidates=[p/(n.replace('.','/')+'.olean') for p in (lib,pack,core) if os.path.lexists(p/(n.replace('.','/')+'.olean'))];assert candidates and candidates[0].is_file() and str(candidates[0])==b['.olean']['path']
 for suffix,v in b.items():
  p=Path(str(candidates[0])[:-6]+suffix)
  if v is None:assert not os.path.lexists(p)
  else:assert p.is_file() and str(p.resolve(strict=True))==v['resolved'] and sha(p)==v['sha256']
print('PASS outer, five stages and all 14 exact axiom reports, 2016 union bundles, 81 outside bundles, first direct selections and all preserved roots')
print('roots',{n:(len(v['project']),len(v['outside'])) for n,v in r['closures'].items()})
