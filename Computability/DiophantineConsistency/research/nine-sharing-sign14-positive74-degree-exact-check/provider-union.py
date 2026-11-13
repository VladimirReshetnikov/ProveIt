#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign14-positive74-degree-translation-check-20261110')/'lib';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
providers=[{'stem': 'nine-sharing-sign14-positive74-degree-identity-check', 'name': 'Sign14Positive74DegreeIdentity', 'root': '/tmp/nine-sharing-sign14-positive74-degree-identity-check-20261110', 'state': 'c6c8735a9c0cf639a97f0605e57e1ec4278bea8f3025b4fdcc425b735049fa04', 'outer': '9bd76935fe1b53ddd0dd34c92b9cd0e68ad5458087fc3ef7264f0aaffad7bc54', 'audit': 'e96dcfa472e30051110caf454dbf495d016ef8b7361dab9a3c62c6759448b67a', 'review': 'nine-sharing-sign14-positive74-degree-identity-terminal-independent'}, {'stem': 'nine-sharing-sign14-86gate-degree-check', 'name': 'Sign14Optimized86Degree', 'root': '/tmp/nine-sharing-sign14-86gate-degree-check-20261110', 'state': '08fe01da36402dc54709f243bbe6949aa87bebb3f7a4cd25412b0c7df540765f', 'outer': '5cd288741bd5ff679478153807eaf49a0f0db3021944a8e23326385cf763d196', 'audit': '0a27be8dce57b5e724d5fd3ab0ecf2cdba5027d26a02effe37288ba612f92c84', 'review': 'nine-sharing-sign14-86gate-degree-terminal-independent'}]
pins={'nine-sharing-sign14-92gate-degree-check': '464fa9acd950e62999b0e59ea500593f69e60804c528ba6a056e94ae5ce15ad8', 'nine-sharing-sign14-93gate-degree-check': 'f59ad09820da9c2e7d8279217e2d4efefc49fc1a8621de6dc4865593e1965935', 'nine-sharing-sign14-94gate-degree-check': 'f5c07c735549560e36da3452355713ace769d3a28f31b30df3ad28f55b2d5565', 'nine-sharing-sign14-95gate-degree-check': '53abe28a728d7970ae2f253eeb1f9debd0ff7dde94962a006d8b5e5a8a046866', 'nine-sharing-sign14-exact-degree-check': '557cf45ada7161171ebb45f3aaf6ca7ee5a23abdc68f1f0ae744f86656c2c092', 'nine-sharing-sign14-axis-seed-degree-check': '7934e6849f35020d2c92333ceb2e3ad9abec43343a22932438eeeab720ace781', 'nine-sharing-sign14-axis-na-binding-check': '51f523000fac1b9a30c6a08bb1ac6c42fb040a931729f389c681855095b25883', 'nine-sharing-sign14-axis-inner-binding-check': 'c256889a4f1e867a06f494ace4f11d535958b50d337d08bf3b18b9c7bd2ef4a6', 'nine-sharing-sign14-axis-binding-check': 'a1f18f05e3004aa824fcdde209ce253d6b502d3e5cfe9cf75400cf591b869057', 'nine-sharing-sign14-axis-na-generic-check': '69c9188c74567ba9a23dec819871913399982d3269697031c33877c82304d32c', 'nine-sharing-sign14-axis-degree-generic-check': 'e6a281780e67108f016bb14ea517a17b5881decb3417f3c40620353f0c7cdebf'}
extra={};direct={};overlap=0
for spec in providers:
 state=D/'research'/spec['stem']/'attempt01/state.json';outer=D/'research'/spec['stem']/'attempt01/outer-result.json';audit=D/'reviews'/spec['review']/'check.py';need(H(state)==spec['state'] and H(outer)==spec['outer'] and H(audit)==spec['audit'],'provider receipt/audit');need(json.loads(outer.read_text())['author_observed_numeric_outer_exit']==0,'outer');d=json.loads(state.read_text());need(d['status']=='PASS' and len(d['rows'])==1,'provider status');r=d['rows'][0];n=spec['name'];root=Path(spec['root']);need(r['module']==n and r['deps']['exit']==0 and r['compile']['exit']==0,'stage');obj=root/'lib/DiophantineConsistency'/(n+'.olean');need(H(obj)==r['object_sha256'] and H(root/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256'],'provider source/object');direct[n]={'realpath':str(obj.resolve()),'sha256':H(obj)}
 for k in ('deps','compile'):need(H(root/(n+'-'+k+'.txt'))==r[k]['log_sha256'],'provider log')
 for path,val in r['direct_guard'].items():
  q=Path(path)
  if val is None:need(not os.path.lexists(q),'guard unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==val['realpath'] and H(q)==val['sha256'],'guard drift '+path)
 entries=dict(d['overlay_links']);entries[str(obj)]=str(obj.resolve())
 for path,real in entries.items():
  q=Path(path);need(q.is_file() and str(q.resolve())==real,'overlay drift '+path);rel=str(q.relative_to(root/'lib'));target=BASE/rel;rec={'realpath':real,'sha256':H(q)}
  if os.path.lexists(target):
   need(target.is_file() and str(target.resolve())==real and H(target)==rec['sha256'],'overlap conflict '+rel);overlap+=1
  else:
   if rel in extra:need(extra[rel]==rec,'extra conflict '+rel)
   else:extra[rel]=rec
edges=[]
for stem,pin in pins.items():
 state=D/'research'/stem/'attempt01/state.json';need(H(state)==pin,'captured state '+stem);d=json.loads(state.read_text());need(d['status']=='PASS','captured status '+stem)
 for r in d['rows']:
  for mod,dep in r['dependencies'].items():
   if mod=='Init':continue
   rel=mod.replace('.','/')+'.olean';q=BASE/rel
   if q.is_file():rec={'realpath':str(q.resolve()),'sha256':H(q)}
   else:need(rel in extra,'missing captured route '+rel);rec=extra[rel]
   need(rec['realpath']==dep['realpath'] and rec['sha256']==dep['sha256'],'captured edge '+r['module']+' '+mod);edges.append((r['module'],mod))
need(any(a=='Sign14ExactDegree' and b.endswith('Sign14AxisDegreeLower') for a,b in edges),'missing lower edge')
print(json.dumps({'status':'PASS','extra':extra,'direct':direct,'overlap_count':overlap,'captured_direct_edges':len(edges),'scope':'two producer union and captured dependency edges at survey time; not a complete transitive trace'},sort_keys=True))
