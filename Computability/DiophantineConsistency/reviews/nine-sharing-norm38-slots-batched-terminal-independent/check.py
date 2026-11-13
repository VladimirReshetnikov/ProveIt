#!/usr/bin/env python3
"""Independent review of the first batched partial terminal artifacts; no Lean."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];root=next(p for p in D.parents if (p/'lakefile.toml').is_file());P=D/'research/nine-sharing-norm38-slots-batched-draft';T=Path('/tmp/nine-sharing-norm38-slots-batched-20261105');A=P/'attempt01';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,s):
 if not x:raise RuntimeError(s)
for p,h in [(P/'run.py','88663c80c9a55fe3b8b1411aec5990a19c44734202f9bdbf624e5530fa96c938'),(P/'source-manifest.json','97c061c885b7be6495b1244713b31fea1ff0ac955b493e066eaa1139c8ab40ac'),(A/'state.json','a8ce8f12f4948c97b8a171e34c3c8c1f652ce03ec6d28251ae82555f6dc4b9f0'),(A/'outer-terminal-author-record.json','d578d5f295b6b494acb721a656856e703d4453a8025e2a4d92e6e3b433d8d675')]:need(sha(p)==h,'pin '+str(p))
need(sha(A/'state.json')==sha(T/'state.json'),'state temp');s=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal-author-record.json').read_text());need(s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38Slots02')" and o['outer_session_id']==38247 and o['outer_exit_code']==1,'outer/state');m=json.loads((P/'source-manifest.json').read_text())['rows'];need(len(m)==12 and len(s['rows'])==4,'counts');source=(D/'research/nine-sharing-norm38-slot-extraction-check/src/DiophantineConsistency/Norm38SlotExtraction.lean').read_text()
for i in range(6):
 name=f'slot{i:02}';one=re.search(r'theorem '+name+r'\b.*? := by',source,re.S);group=(P/f'src/DiophantineConsistency/Norm38Slots{i//3:02}.lean').read_text();two=re.search(r'theorem '+name+r'\b.*? := by',group,re.S);need(one and two and one.group()==two.group(),'statement '+name)
for path,target in s['overlay_links'].items():need(Path(path).is_symlink() and str(Path(path).resolve())==target,'overlay '+path)
counts=0;warnings=0
for i,(row,entry) in enumerate(zip(s['rows'],m)):
 n=row['module'];need(n==['Norm38SlotsBase','Norm38Slots00','Norm38Slots01','Norm38Slots02'][i] and entry['module']=='DiophantineConsistency.'+n,'stage');src=P/'src/DiophantineConsistency'/(n+'.lean');need(sha(src)==sha(root/entry['source'])==sha(T/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']==entry['source_sha256'],'source '+n);need(re.findall(r'^import ([A-Za-z0-9_.]+)$',src.read_text(),re.M)==entry['imports'],'imports '+n)
 for typ in ('deps','compile'):
  v=row[typ];need(v['exit']==(1 if i==3 and typ=='compile' else 0) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'],'monitor '+n+typ);log=A/(n+'-'+typ+'.txt');need(sha(log)==sha(T/(n+'-'+typ+'.txt'))==v['log_sha256'],'log '+n+typ)
  if typ=='compile':warnings+=len(re.findall('warning:',log.read_text()))
 for path,v in row['direct_guard'].items():
  counts+=1;f=Path(path)
  if v is None:need(not os.path.lexists(f),'absence '+path)
  else:need(f.is_file() and str(f.resolve())==v['realpath'] and sha(f)==v['sha256'],'guard '+path)
 for mod,dep in row['dependencies'].items():
  f=Path(dep['path']);need(f.is_file() and str(f.resolve())==dep['realpath'] and sha(f)==dep['sha256'],'dep '+mod)
  if mod=='DiophantineConsistency.Norm38SlotsBase':need(dep['sha256']==s['rows'][0]['object_sha256'],'base route')
 if i<3:need(sha(T/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'],'object '+n)
 else:
  log=(A/(n+'-compile.txt')).read_text();need(not row.get('object_sha256') and sha(A/(n+'-compile.txt'))=='f6dd6ec40626bdbd002d5e2fd355fcbbe9001e9ba1e3da02795a777c23ba7a22' and 'error: unsolved goals' in log and 'ι 4' in log and 'ι 3' in log,'numeral failure')
print(json.dumps({'status':'PASS_SCOPED_PARTIAL_TERMINAL_REVIEW','successful_stages':3,'successful_slots':6,'failed_group':'Norm38Slots02','guards':counts,'overlay_links':len(s['overlay_links']),'warning_entries':warnings,'outer':'author-recorded 38247 exit 1','scope':'Retained artifacts/source, no Lean replay, no claim for later stages or complete extraction.'},indent=2,sort_keys=True))
