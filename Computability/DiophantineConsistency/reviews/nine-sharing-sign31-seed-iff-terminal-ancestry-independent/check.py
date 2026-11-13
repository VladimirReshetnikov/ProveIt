#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-seed-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-seed-iff-check-20261106');B=Path('/tmp/nine-sharing-sign31-zero-bridge-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(A/'state.json')=='ae407f3085a083ee4eb4bff28e64a4cdcd698cac3b87bdb3a0163e231f86f511';assert H(A/'outer-result.json')=='83f8cf5058894bd13f47437782bdfdf7089656568738077dbc9208d2a675ac4c'
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-result.json').read_text());assert d['status']=='PASS' and len(d['rows'])==2 and o['author_observed_numeric_outer_exit']==0 and o['author_observed_outer_session']==58566;assert H(P/'run.py')==d['runner_sha256']=='ab07005e420055cba00e364ce0abe3b1c7c3231af4ac8c80b463b576111d39f5'
def guards(row):
 for k,v in row['direct_guard'].items():
  q=Path(k)
  if v is None:assert not os.path.lexists(q),k
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],k
def rows(data,root,retained=None):
 for row in data['rows']:
  n=row['module'];assert row['deps']['exit']==row['compile']['exit']==0 and row['deps']['stop_reason'] is None and row['compile']['stop_reason'] is None
  for k in ('deps','compile'):assert not row[k]['monitor_errors'] and not row[k]['observed_descendant_pids']
  assert H(root/'src/DiophantineConsistency'/f'{n}.lean')==row['source_sha256'] and H(root/'lib/DiophantineConsistency'/f'{n}.olean')==row['object_sha256']
  for k in ('deps','compile'):
   assert H(root/f'{n}-{k}.txt')==row[k]['log_sha256']
   if retained:assert H(retained/f'{n}-{k}.txt')==row[k]['log_sha256']
  for k,v in row['dependencies'].items():
   q=Path(v['path']);assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'];assert row['direct_guard'][v['path']]=={'realpath':v['realpath'],'sha256':v['sha256']}
  guards(row)
rows(d,O,A)
for k,v in d['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
base=D/'research/nine-sharing-sign31-zero-bridge-check/attempt01/state.json';assert H(base)==d['base_state_sha256']=='fa1c8aeef56d0ca8dba24389602f4862518cc5589ac58d51ca0984fbea25fc6b';bd=json.loads(base.read_text());assert bd['status']=='PASS' and len(bd['rows'])==4;rows(bd,B)
for n in ['Sign31SeedPointwise','Sign31SeedExistential']:
 assert H(P/'src/DiophantineConsistency'/f'{n}.lean')==next(r['source_sha256'] for r in d['rows'] if r['module']==n)
 text=(A/f'{n}-compile.txt').read_text();assert not re.search(r'warning:|error:|sorryAx',text);assert text.count('[propext, Classical.choice, Quot.sound]')==(2 if n=='Sign31SeedPointwise' else 1)
survey=P/'first-cut-survey.py';assert H(survey)=='a1bb29c1a7fb7eca8b12e63d4e1cb06fbaa47eec509fc35175f65e55cb346f41';r=subprocess.run([sys.executable,'-I','-S','-B',str(survey)],capture_output=True,text=True,timeout=120);assert r.returncode==0 and json.loads(r.stdout)['status']=='PASS'
print(json.dumps({'status':'PASS','terminal_stages':2,'candidate_guard_slots':sum(len(x['direct_guard']) for x in d['rows']),'overlay_links':len(d['overlay_links']),'producer_rows':4,'first_cut_survey_exit':r.returncode,'scope':'No Lean replay; outer exit author-recorded; deeper dynamic/transitive ancestry inherited.'},sort_keys=True))
