import json,pathlib,shutil
A=pathlib.Path('/tmp/ipra-bounded-induction-postmerge-2qjq8sdo');B=pathlib.Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');D=pathlib.Path('reviews/ipra-bounded-induction-postmerge-replay');a=json.loads((A/'state.json').read_text());b=json.loads((B/'state.json').read_text())
for k in ['parent','parent_state_sha256','manifest_sha256','driver_sha256','scope']:assert a[k]==b[k],k
assert len(a['records'])==len(b['records'])==41 and a['status']==b['status']=='PASS'
def norm(v,root):
 p=pathlib.Path(v)
 try:return '$BUILD/'+str(p.relative_to(root))
 except ValueError:return str(p)
for x,y in zip(a['records'],b['records']):
 assert all(x[k]==y[k] for k in ['name','exit','object_sha256','log_sha256']),x['name']
 assert set(x['direct_imports'])==set(y['direct_imports']),x['name']
 for k in x['direct_imports']:
  p=x['direct_imports'][k];q=y['direct_imports'][k];assert p['sha256']==q['sha256'],(x['name'],k)
  assert norm(p['resolved_path'],A)==norm(q['resolved_path'],B),(x['name'],k,p,q)
for label,p in [('author',A),('independent',B)]:
 shutil.copy2(p/'state.json',D/(label+'-state.json'));d=D/(label+'-logs');d.mkdir(exist_ok=True)
 for row in a['records']:shutil.copy2(p/'logs'/(row['name']+'.log'),d/(row['name']+'.log'))
print('MATCH',len(a['records']),'rows and all direct import hashes/resolved paths')
