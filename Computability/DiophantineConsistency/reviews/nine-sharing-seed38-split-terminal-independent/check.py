#!/usr/bin/env python3
"""Read-only audit of split experiment terminal evidence; no Lean launch."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-seed38-split-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-seed38-split-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='b1dc0d908a26bfdc3a657a29ae9cb7b98a3d6b10e560a04e5b245903b4057814'
assert sha(q/'run.py')=='17dda5818da1a84875d6213cf2b0a080ffce99585294231524199b905998cc0c'
assert sha(q/'source-manifest.json')=='c4ce5fd28170206e920d1f2f755d995225c40c1eef53d1a0a1d8c76020af03fa'
assert sha(a/'SharingSeed38Weighted-compile.txt')=='c5b6a9ac4d5c330c444ea239614463ef7babc6a6b7f7415af348beda30d19ced'
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed SharingSeed38Weighted')"
outer=json.loads((a/'outer-terminal-author-record.json').read_text());assert outer['outer_session_id']==55616 and outer['outer_exit_code']==1 and 'not independently observed' in outer['observation_kind']
manifest=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(manifest)==10
for e in manifest:assert sha(q/'src/DiophantineConsistency'/(e['module'].split('.')[-1]+'.lean'))==e['source_sha256']
prior=(D/'research/nine-sharing-seed38-lean-draft/SharingSeed38.lean').read_text()
def declaration(text,kind,name):
 m=re.search(r'^'+kind+' '+name+r'\b.*?(?=^/--|^def |^theorem |^-- Unresolved:|^end )',text,re.M|re.S);assert m,(kind,name);return m.group(0).strip()
syntax=(q/'src/DiophantineConsistency/SharingSeed38Syntax.lean').read_text();norm=(q/'src/DiophantineConsistency/SharingSeed38Normalize.lean').read_text()
for name in ('firstResidual','remainingResiduals','seed','zeroWitness'):assert declaration(prior,'def',name)==declaration(syntax,'def',name)
for name in ('firstResidual_zeroWitness','eval_sumSquares_nonneg','seed_normalized'):assert declaration(prior,'theorem',name)==declaration(norm,'theorem',name)
names=['SharingGateModel','ForwardWitness38','SharingSeed38Syntax','SharingSeed38Normalize','SharingSeed38Weighted'];assert [x['module'] for x in s['rows']]==names
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
for row in s['rows']:
 n=row['module'];assert row['source_sha256']==sha(q/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
 for typ in ('deps','compile'):
  r=row[typ];check(a/(n+'-'+typ+'.txt'),r['log_sha256']);check(out/(n+'-'+typ+'.txt'),r['log_sha256']);assert not r['monitor_errors'] and not r['observed_descendant_pids']
 assert row['deps']['exit']==0 and row['deps']['stop_reason'] is None
 for k,v in row['direct_guard'].items():
  if v is None:assert not os.path.lexists(k)
  else:check(k,v['sha256'],v['realpath'])
 for v in row['dependencies'].values():check(v['path'],v['sha256'],v['realpath'])
 if 'object_sha256' in row:check(out/'lib/DiophantineConsistency'/(n+'.olean'),row['object_sha256'])
for row in s['rows'][:4]:assert row['compile']['exit']==0 and row['compile']['stop_reason'] is None and 'object_sha256' in row
bad=s['rows'][4]['compile'];assert bad['exit']==1 and bad['stop_reason'] is None and bad['timeout_seconds']==120
assert 'error: unsolved goals' in (a/'SharingSeed38Weighted-compile.txt').read_text()
assert (a/'SharingGateModel-compile.txt').read_text().count('This simp argument is unused:')==2
print(json.dumps({'status':'PASS_RETAINED_SPLIT_TERMINAL_AUDIT','state_sha256':sha(a/'state.json'),'outer_author_record_sha256':sha(a/'outer-terminal-author-record.json'),'author_recorded_outer_session':55616,'author_recorded_outer_exit':1,'successful_modules':{r['module']:r['object_sha256'] for r in s['rows'][:4]},'failed_module':names[4],'failed_compile_exit':1,'failed_stop_reason':None,'direct_guard_slots':sum(len(r['direct_guard']) for r in s['rows']),'overlay_links':len(s['overlay_links']),'scope':'Retained state/logs, exact declaration comparisons and live direct guards; no Lean replay or independent observation of past outer exit.'},indent=2,sort_keys=True))
