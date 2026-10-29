from pathlib import Path
import json,hashlib,zipfile,subprocess,re
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-window-rem-bound-evidence');b=json.loads((p/'BUNDLE.json').read_text());arc=p/b['archive'];H=lambda v:hashlib.sha256(v).hexdigest();assert H(arc.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(arc) as z:
 assert z.testzip() is None;names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  d=z.read(n);x=b['members'][n];assert len(d)==x['bytes'] and H(d)==x['sha256'];assert not n.endswith(('.olean','.ilean','.o','.c'))
 print('ZIP CRC/archive hash,',len(names),'manifest hashes/sizes; no compiled objects')
 review=(p/b['independent_review']['file']).read_bytes();assert H(review)==b['independent_review']['sha256']==H(z.read('independent/window-rem-independent-review.txt'));print('standalone and archived review match')
 c=b['source_commit'];parent=b['source_parent'];assert subprocess.check_output(['git','rev-parse',c+'^'],text=True).strip()==parent;prefix='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 for ph,ref in [('baseline',parent),('final',c)]:
  data=subprocess.check_output(['git','show',ref+':'+prefix+'ArithmeticWindowInterface.lean']);assert data==z.read(f'commit/{ph}.lean');print('git source',ph,H(data))
 assert z.read('prototype/baseline.lean')==z.read('commit/baseline.lean')
 rd=lambda n:json.loads(z.read(n));prior=rd('provider/mask-ins-simplify/independent-direct-provider-audit.json');extras={}
 for f,n,phase,sk in [('provider/mask-ins-simplify/records.json','ArithmeticMaskConstants','final','before'),('provider/binom-odd-sharing/final-records.json','ArithmeticHalfBinomial2011','final','before'),('provider/source-clean/records.json','ArithmeticCurrentSentence2011','final','source_sha256_before')]:
  x=next(x for x in rd(f) if x.get('module',x.get('name'))==n and x.get('phase')==phase and x.get('status')==0);extras[n]=(x[sk],x['object_sha256'])
 rows={};count=0
 for ph in ('baseline','final'):
  for x in rd(f'prototype/{ph}-records.json'):
   n=x['module'];assert x['phase']==ph and x['status']==0 and x['source_before']==x['source_after']
   src=z.read('commit/'+ph+'.lean') if n=='ArithmeticWindowInterface' else subprocess.check_output(['git','show',c+':'+prefix+n+'.lean']);assert x['source_before']==H(src)
   original=z.read('commit/baseline.lean') if n=='ArithmeticWindowInterface' else src;assert x['workspace_before']==x['workspace_after']==H(original)
   assert x['log_sha256']==H(z.read('prototype/'+Path(x['log']).name)) and x['time_sha256']==H(z.read('prototype/'+Path(x['time']).name)) and x['object_sha256']
   for d in x['direct_inputs']:
    m=d['module'].split('.')[-1];assert d['object_before']==d['object_after'] and d['source_before']==d['source_after']
    if m=='ArithmeticWindowInterface':assert d['resolved']==rows[(ph,m)]['object'] and d['object_before']==rows[(ph,m)]['object_sha256'] and d['source_before']==H(z.read('commit/baseline.lean'))
    else:
     source=H(subprocess.check_output(['git','show',c+':'+prefix+m+'.lean']));assert d['source_before']==source
     if m in extras:assert (d['source_before'],d['object_before'])==extras[m]
     else:q=prior[d['module']];assert (d['source_before'],d['object_before'])==(q['source_sha256'],q['object_sha256']) and q['matching_prior_rows']
    count+=1
   rows[(ph,n)]=x
  for x in rd(f'prototype/{ph}-probes.json'):
   assert x['status']==0 and x['source_before']==x['source_after']==H(z.read('prototype/'+Path(x['source']).name)) and x['object_before']==x['object_after']==rows[(ph,'ArithmeticWindowInterface')]['object_sha256'] and x['log_sha256']==H(z.read('prototype/'+Path(x['log']).name)) and x['time_sha256']==H(z.read('prototype/'+Path(x['time']).name))
 print(len(rows),'builds',count,'direct inputs and six probe receipts match source/log/provider records')
 assert rows['baseline','ArithmeticWindowZero']['object_sha256']==rows['final','ArithmeticWindowZero']['object_sha256'];print('WindowZero client object hashes identical')
 def parse(n):return {m.group(1):m.group(0) for m in re.finditer(r'^DECL (\S+) TYPE .*?(?=^DECL |\Z)',z.read(n).decode(),re.M|re.S)}
 a=parse('prototype/baseline-interfaces.log');d=parse('prototype/final-interfaces.log');assert a==d and len(a)==43;print('43 target declaration/type/axiom reports identical')
 for n in ('simp','instances'):
  a=z.read('prototype/baseline-'+n+'.log');d=z.read('prototype/final-'+n+'.log');assert a==d;print(n,'identical',len(a.splitlines()))
 print('Limit: object bytes omitted; first-provider resolution/object bytes supported by receipts, not independently rechecked from archive. Five direct provider matches depend on archived independent audit summary whose underlying historical receipt files are outside this bundle. Other direct client not rebuilt; older transitive objects and packages cached.')
