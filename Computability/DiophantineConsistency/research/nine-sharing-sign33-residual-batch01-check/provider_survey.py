#!/usr/bin/env python3
"""Point-in-time selected producer and overlay survey; no Lean."""
from pathlib import Path
import hashlib,json,os,sys
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1]
def need(x,s):
 if not x: raise RuntimeError(s)
cache={}
def sha(p):
 p=Path(p);rp=str(p.resolve());need(p.is_file(),'missing '+str(p))
 if rp not in cache:cache[rp]=hashlib.sha256(p.read_bytes()).hexdigest()
 return cache[rp]
def verify_guard(g):
 for k,v in g.items():
  p=Path(v.get('path',k.rsplit(':',1)[-1]) if v else k.rsplit(':',1)[-1])
  if v is None:need(not os.path.lexists(p),'unexpected '+k)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'guard drift '+k)
providers=[
 ('terminal','research/nine-sharing-norm38-reference-terminals-check/attempt01/state.json','f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8','/tmp/nine-sharing-norm38-reference-terminals-check-20261105','PASS',1),
 ('fields','research/nine-sharing-norm38-reference-fields-combine-check/attempt01/state.json','7bd683c7d990981e7b1172c16c73c294a4da4f88382949da0d88158c5c580fbc','/tmp/nine-sharing-norm38-reference-fields-combine-check-20261105','FAILED',1),
 ('gates','research/nine-sharing-norm38-forward-gates-draft/attempt01/state.json','42bf82193bf5eef3af518b5a6cffb240ab531975e82fd42afb2e531f675cc07c','/tmp/nine-sharing-norm38-forward-gates-20261105','PASS',13),
 ('prefix','research/nine-sharing-norm38-forward-prefix-check/attempt01/state.json','71326dc89477d47cca893654dca94000877096b87a28ffd1086649677aa52d71','/tmp/nine-sharing-norm38-forward-prefix-check-20261105','PASS',1),
 ('static','research/nine-sharing-norm38-static-to-seed-retry01/attempt01/state.json','ae9f8310391bea63f5d591966b81284846bbf0f526c1da00c8a4225fb56c0b74','/tmp/nine-sharing-norm38-static-to-seed-retry01-20261105','PASS',1),
 ('normfixed','research/nine-sharing-norm38-fixed-port-norms/attempt01/state.json','fa850b4ce480ff0f43c38bbaeca4643a90641f7246aa4d3380070c6fc2fc64a8','/tmp/nine-sharing-norm38-fixed-port-norms-20261106','PASS',1),
 ('sourcepartial','research/nine-sharing-norm38-source-to-seed-staged/attempt01/state.json','94bb5144f566046c47841eb77a35b57b752e8f46d0fccd4cf75f4b44fcc7aeae','/tmp/nine-sharing-norm38-source-to-seed-staged-20261105','FAILED',1),
 ('castfree','research/nine-sharing-norm38-current-castfree-iff-draft/attempt01/state.json','668decb8f55d4566093bdfd08b448bfb4affeb7cec695f7df23f1b8f7a8183cd','/tmp/nine-sharing-norm38-current-castfree-iff-check-20261106','PASS',1),
 ('windows','research/nine-sharing-sign33-windows-retry01/attempt01/state.json','9bba240fcea1e0efc75c9c8022016c61b68a0dfeabb05d66ea4b28786899faa1','/tmp/nine-sharing-sign33-windows-retry01-20261106','PASS',1),
 ('strongf','research/nine-sharing-sign33-strong-f-retry01/attempt01/state.json','2c513f2262b81f9b0e7d0da8b704dab73da0820a7a339ef9158a3eddc3b06a2c','/tmp/nine-sharing-sign33-strong-f-retry01-20261106','PASS',1),
 ('absdiff','research/nine-sharing-sign33-absdiff-square-check/attempt01/state.json','0adb930ca2a8ae278945357cbdedb3636c93014b57cdcd85ddfe24edcece0fff','/tmp/nine-sharing-sign33-absdiff-square-check-20261106','PASS',1),
 ('gaptau','research/nine-sharing-sign33-gap-tau-ring-retry02/attempt01/state.json','2293a07d5a524c81ef739382ed92bda7e1e553bf7af9e9b2f031069e8a389299','/tmp/nine-sharing-sign33-gap-tau-ring-retry02-20261106','PASS',1),
 ('innerv','research/nine-sharing-sign33-inner-v-ring-check/attempt01/state.json','2c4ed1f6ee2dd1588d0c1b1d2a4121f0f07e1a38bac2fe53b317d73153b43c2a','/tmp/nine-sharing-sign33-inner-v-ring-check-20261106','PASS',1),
 ('auxring','research/nine-sharing-sign33-aux-ring-retry01/attempt01/state.json','cf7ac3aa5c46fd4dc3eb6cd3da2b5009aea19a104fc710b098244b53155b40de','/tmp/nine-sharing-sign33-aux-ring-retry01-20261106','PASS',1),
 ('currentwindows','research/nine-sharing-sign33-current-windows-check/attempt01/state.json','ed0ee11bdf097d8d844da870cd9c2191f861d7e7f5e23bdf53114648f1bf64db','/tmp/nine-sharing-sign33-current-windows-check-20261106','PASS',1),
 ('fivewitnesses','research/nine-sharing-sign33-five-witnesses-check/attempt01/state.json','933c9733daeaa2c705fbb1a5b1c3c95c4ab37d078a9c9b3bfc839d39b469253e','/tmp/nine-sharing-sign33-five-witnesses-check-20261106','PASS',1),
 ('seedsquares','research/nine-sharing-sign33-seed-squares-check/attempt01/state.json','b1baa34a7e28603de20eb013e1b6b14e456c3d1ea982cb72a2216ff90a1a1ab0','/tmp/nine-sharing-sign33-seed-squares-check-20261106','PASS',1),
 ('firstcut','research/nine-sharing-sign33-first-cut-retry01/attempt01/state.json','e4a8cac08edb420ebbbc5ab1d77fa8e553037aba3fcf46498ab40adec0c1ea3f','/tmp/nine-sharing-sign33-first-cut-retry01-20261106','PASS',1),
 ('forwardpartial','research/nine-sharing-norm38-forward-source-check/attempt01/state.json','cab44da16e5312c579738b4367e8d62b701654aff502e529a3bfd0f30744c58c','/tmp/nine-sharing-norm38-forward-source-check-20261105','FAILED',1)]
links={};selected={};counts={}
def add(rel,p):
 p=Path(p);rp=str(p.resolve());h=sha(p)
 if rel in links:need(links[rel]['sha256']==h,'overlay object conflict '+rel)
 else:links[rel]={'realpath':rp,'sha256':h}
for label,relative,pin,root,status,count in providers:
 state=D/relative;root=Path(root);need(sha(state)==pin,'provider state '+label);d=json.loads(state.read_text());need(d['status']==status,'provider status '+label);need(len(d['rows'])==count+(1 if label in ('fields','forwardpartial','sourcepartial') else 0),'provider rows '+label)
 if label=='fields':need(d['rows'][1]['module']=='Norm38StaticCarrierConditional' and d['rows'][1]['compile']['exit']==1,'failed fields row')
 if label=='sourcepartial':need(d['rows'][1]['module']=='Norm38CarrierUnitNorms' and d['rows'][1]['compile']['stop_reason']=='timeout','failed sourcepartial row')
 if label=='forwardpartial':need(d['rows'][1]['module']=='Norm38SourceToSeed' and d['rows'][1]['compile']['stop_reason']=='timeout','failed forward row')
 for k,v in d['overlay_links'].items():
  q=Path(k);need(q.is_symlink() and str(q.resolve())==v,'provider overlay '+k);rel=str(q.relative_to(root/'lib'));add(rel,q)
 for row in d['rows'][:count]:
  n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0 and row['compile']['stop_reason'] is None,'provider stage '+n);src=root/'src/DiophantineConsistency'/(n+'.lean');obj=root/'lib/DiophantineConsistency'/(n+'.olean');need(sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'],'provider source/object '+n)
  for phase in ('deps','compile'):need(sha(root/(n+'-'+phase+'.txt'))==row[phase]['log_sha256'],'provider log '+n)
  verify_guard(row['direct_guard']);add('DiophantineConsistency/'+n+'.olean',obj)
  if n in ('Norm38ReferenceTerminals','Norm38ReferenceFieldsAll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix','Norm38StaticToSeed','Norm38ForwardFiveNorms','Norm38FixedPortNorms','Norm38SourceCarrierZero','Norm38CurrentCastFreeIff','Sign33Windows','Sign33StrongF','Sign33AbsDiffSquare','Sign33GapTauRing','Sign33InnerVRing','Sign33AuxRing','Sign33CurrentWindows','Sign33FiveWitnesses','SharingSign33Squares','Sign33FirstCut'):selected['DiophantineConsistency.'+n]={'sha256':row['object_sha256'],'realpath':str(obj.resolve())}
 counts[label]={'rows':count,'overlay_links':len(d['overlay_links'])}
need(len(selected)==19,'selected objects')
sphere=D/'research/current2011-spheres-fresh-base/attempt02/result.json';sr=Path('/tmp/current2011-spheres-fresh-base-priority-check02');need(sha(sphere)=='67159c8c4665700e59c6745b705f42ecc459ca6a38f79bd95545c8e7115c31d9'==sha(sr/'result.json'),'sphere receipt');sd=json.loads(sphere.read_text());need(sd['status']=='PASS' and sd['exit']==0 and sd['guards_stable'] and sd['guards_before']==sd['guards_after'],'sphere status');verify_guard(sd['guards_after']);need(sha(sr/'compile.log')==sd['log_sha256'] and sha(sr/'FreshCarrierSpheres.olean')==sd['object_sha256']=='37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020','sphere object/log');selected['FreshCarrierSpheres']={'sha256':sd['object_sha256'],'realpath':str((sr/'FreshCarrierSpheres.olean').resolve())}
model=D/'research/normalized106-fresh-base-model-build/attempt03/state.json';mr=Path('/tmp/normalized106-fresh-model-client-20261105');need(sha(model)=='dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23'==sha(mr/'state.json'),'model receipt');md=json.loads(model.read_text());need(md['status']=='PASS' and len(md['runs'])==2 and all(x['exit']==0 for x in md['runs']),'model status');need(sha(mr/'FreshModel106.lean')==md['source_sha256'] and sha(mr/'FreshModel106.olean')==md['object_sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','model source/object');need(sha(mr/'deps.txt')==md['runs'][0]['log_sha256'] and sha(mr/'compile.txt')==md['runs'][1]['log_sha256'],'model logs');verify_guard(md['direct_guard']);selected['FreshModel106']={'sha256':md['object_sha256'],'realpath':str((mr/'FreshModel106.olean').resolve())}
for n in ('Norm38CarrierUnitNorms','Norm38SourceToSeed','Sign33ResidualBatch00','Sign33ResidualBatch01'):need('DiophantineConsistency/'+n+'.olean' not in links,'candidate target collision '+n)
# Authenticate the exact three endpoint-provider rows and an earlier successful consumer.
current=Path('/tmp/current14-standard-fresh-build-20261104');cs=current/'state.json'
need(sha(cs)=='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014','current base receipt');cd=json.loads(cs.read_text());need(cd['status']=='PASS','current base status')
for name in ('HACurrentEquation2011','IPRAStandardTheory','ArithmeticPellFirstIndex','ArithmeticCarrierSoundness2011'):
 mod='DiophantineConsistency.'+name; rows=[r for r in cd['records'] if r['module']==mod];need(len(rows)==1,'current row '+mod);row=rows[0]
 src=Path(cd['snapshot'])/'src/DiophantineConsistency'/(name+'.lean');obj=current/'lib/DiophantineConsistency'/(name+'.olean')
 need(row['exit']==0 and sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(row['log'])==row['log_sha256'],'current producer '+mod)
 for inp in row['direct_inputs'].values():need(sha(inp['path'])==inp['sha256'],'current producer input '+mod)
 add('DiophantineConsistency/'+name+'.olean',obj);selected[mod]={'sha256':row['object_sha256'],'realpath':str(obj.resolve())}
modelroot=Path('/tmp/normalized106-fresh-model-build-v2-20261105');ms=modelroot/'state.json';need(sha(ms)=='c42e5d49c4234ff93e61b7dbadf63fe8e2d465f470f4772879694796d898272c','native producer receipt');md2=json.loads(ms.read_text());need(md2['status']=='FAILED' and md2['records'][-1]['module']=='FreshModel106' and md2['records'][-1]['compile']['exit']==1,'native failed sibling')
mod='DiophantineConsistency.IPRAExpressionNative';rows=[r for r in md2['records'] if r['module']==mod];need(len(rows)==1,'native row');row=rows[0];src=modelroot/'src/DiophantineConsistency/IPRAExpressionNative.lean';obj=modelroot/'lib/DiophantineConsistency/IPRAExpressionNative.olean'
need(row['deps_run']['exit']==0 and row['compile']['exit']==0 and sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'],'native producer source/object');need(sha(row['deps_run']['log'])==row['deps_run']['log_sha256'] and sha(row['compile']['log'])==row['compile']['log_sha256'],'native producer logs');verify_guard(row['guard']);add('DiophantineConsistency/IPRAExpressionNative.olean',obj);selected[mod]={'sha256':row['object_sha256'],'realpath':str(obj.resolve())}
# Authenticate the successful ModelDifferenceRing row of the same failed build.
mod='DiophantineConsistency.ModelDifferenceRing';rows=[r for r in md2['records'] if r['module']==mod];need(len(rows)==1,'model ring row');row=rows[0];src=modelroot/'src/DiophantineConsistency/ModelDifferenceRing.lean';obj=modelroot/'lib/DiophantineConsistency/ModelDifferenceRing.olean'
need(row['deps_run']['exit']==0 and row['compile']['exit']==0 and sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'],'model ring source/object');need(sha(row['deps_run']['log'])==row['deps_run']['log_sha256'] and sha(row['compile']['log'])==row['compile']['log_sha256'],'model ring logs');verify_guard(row['guard']);add('DiophantineConsistency/ModelDifferenceRing.olean',obj);selected[mod]={'sha256':row['object_sha256'],'realpath':str(obj.resolve())}
consumer=D/'research/nine-current-lightweight-endpoint-retry/attempt02/state.json';need(sha(consumer)=='00149b46384d4263ba6ddee3af1d09576735342b0bd58ac4a019438d8f1fffe6','consumer receipt');co=json.loads(consumer.read_text());need(co['status']=='PASS' and len(co['rows'])==1,'consumer status');cr=co['rows'][0];need(cr['deps']['exit']==0 and cr['compile']['exit']==0,'consumer exits')
for name in ('HACurrentEquation2011','IPRAExpressionNative','IPRAStandardTheory'):
 mod='DiophantineConsistency.'+name;observed=cr['dependencies'][mod];need(observed['sha256']==selected[mod]['sha256'] and observed['realpath']==selected[mod]['realpath'],'consumer route '+mod)
# The standalone ordered-ring provider is a top-level module.
stand=D/'research/sign33-ordered-ring-standalone-check/attempt01/state.json';root=Path('/tmp/sign33-ordered-ring-standalone-check-20261106');need(sha(stand)=='e6f245013055355451ee1411f0a5eed07e5815579a7741e2fddbb3f64446965a','ordered ring receipt');od=json.loads(stand.read_text());need(od['status']=='PASS' and len(od['rows'])==1,'ordered ring status');row=od['rows'][0];obj=root/'lib/Sign33OrderedRing.olean';src=root/'src/Sign33OrderedRing.lean';need(row['module']=='Sign33OrderedRing' and row['deps']['exit']==0 and row['compile']['exit']==0 and row['compile']['stop_reason'] is None,'ordered ring exits');need(sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'],'ordered ring source/object')
for phase in ('deps','compile'):need(sha(root/('Sign33OrderedRing-'+phase+'.txt'))==row[phase]['log_sha256'],'ordered ring logs')
verify_guard(od['direct_guard']);add('Sign33OrderedRing.olean',obj);selected['Sign33OrderedRing']={'sha256':row['object_sha256'],'realpath':str(obj.resolve())}
print(json.dumps({'status':'PASS_POINT_PRODUCER_SURVEY','providers':counts,'links':links,'selected':selected,'scope':'Selected source/object/log/direct-guard and overlay observations only; no Lean or complete transitive/dynamic ancestry.'},sort_keys=True))
