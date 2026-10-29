from pathlib import Path
import hashlib,json,re,subprocess,zipfile
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();assert h((r/m['archive']).read_bytes())==m['archive_sha256'] and h((r/m['independent_review']['path']).read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(r/m['archive']) as z:
 ns=z.namelist();assert len(ns)==len(set(ns)) and set(ns)==set(m['members']) and z.testzip() is None
 for n,meta in m['members'].items():
  b=z.read(n);assert len(b)==meta['bytes'] and h(b)==meta['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 rec={}; names=['ArithmeticWindowDigits','ArithmeticCyclicWord','ArithmeticMaskConstants','ArithmeticWindowBits']
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  name='ArithmeticWindowDigits.lean';x=z.read('commit/'+ph+'/'+name);assert x==z.read('prototype/'+ph+'/DiophantineConsistency/'+name)==subprocess.check_output(['git','show',rev+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name])
  rows=json.loads(z.read('prototype/'+ph+'-records.json'));assert [x['module'] for x in rows]==names;rec[ph]={x['module']:x for x in rows}
  for x in rows:
   assert x['status']==0 and x['phase']==ph and x['before']==x['after']==h(z.read('prototype/'+ph+'/DiophantineConsistency/'+x['module']+'.lean'))
   assert x['log_sha256']==h(z.read('prototype/'+ph+'-'+x['module']+'.log')) and x['time']==z.read('prototype/'+ph+'-'+x['module']+'.time').decode()
   for d in x['inputs']:
    assert d['before']==d['after'] and d['source_before']==d['source_after'];n=d['module'].split('.')[-1]
    if n=='ArithmeticWindowDigits':assert d['before']==rec[ph][n]['object_sha256'] and d['source_before']==h(z.read('commit/baseline/'+n+'.lean'))
    elif d['source_before'] is not None:assert d['source_before']==h(z.read('sources/'+n+'.lean'))
 probes=json.loads(z.read('prototype/probe-records.json'));assert len(probes)==16
 for x in probes:
  ph=x['phase'];assert x['status']==0 and x['source_before']==x['source_after']==h(z.read('prototype/'+Path(x['source']).name)) and x['log_sha256']==h(z.read('prototype/'+Path(x['log']).name)); objs=[rec[ph]['ArithmeticWindowDigits']['object_sha256']]+([rec[ph]['ArithmeticCyclicWord']['object_sha256']] if x['module']=='ArithmeticCyclicWord' else []);assert x['before']==x['after']==objs
 for name in ('ArithmeticWindowDigits','ArithmeticCyclicWord'):
  for k in ('names','interfaces','simp','instances'):assert z.read('prototype/baseline-'+name+'-'+k+'.log')==z.read('prototype/final-'+name+'-'+k+'.log')
 for name in ('ArithmeticMaskConstants','ArithmeticWindowBits'):assert rec['baseline'][name]['object_sha256']==rec['final'][name]['object_sha256']
 for name in ('ArithmeticWindowDigits','ArithmeticMaskConstants','ArithmeticWindowBits'):
  for ph in ('baseline','final'):assert not z.read('prototype/'+ph+'-'+name+'.log')
 def warning(ph):return re.sub(r'/dev/shm/window-positive/(baseline|final)/DiophantineConsistency/','SOURCE/',z.read('prototype/'+ph+'-ArithmeticCyclicWord.log').decode())
 assert warning('baseline')==warning('final') and warning('final').count('warning:')==1
 producers={'ArithmeticRepunit':'binary-half-final-records.json','ArithmeticBinaryCarry':'binary-half-final-records.json','ArithmeticStandardCasts':'binary-half-supplement-records.json','ArithmeticMaskData':'transport-assembly-common-records.json','ArithmeticMaskKernel':'transport-assembly-common-records.json'}
 for n,f in producers.items():
  d=next(d for x in rec['baseline'].values() for d in x['inputs'] if d['module'].split('.')[-1]==n);rows=json.loads(z.read('providers/'+f));matches=[x for x in rows if x.get('module','').split('.')[-1]==n and x.get('status')==0 and x.get('object_sha256')==d['before']];assert matches;x=matches[-1];before=x.get('source_before',x.get('before',x.get('source_sha256')));after=x.get('source_after',x.get('after',x.get('source_sha256')));assert before==after==d['source_before']
print('PASS',len(m['members']),'members, snapshots, builds, probes, warnings and five direct provider associations')
