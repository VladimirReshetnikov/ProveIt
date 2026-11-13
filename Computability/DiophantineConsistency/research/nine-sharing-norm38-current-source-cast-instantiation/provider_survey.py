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
 ('currentsource','research/nine-sharing-norm38-current-source-to-seed/attempt01/state.json','706bff9dd72de8b197bca5e69a7a0b91f6138dd7741bf419115865ac94612eb6','/tmp/nine-sharing-norm38-current-source-to-seed-20261106','PASS',1),
 ('fourvar','research/nine-sharing-norm38-four-variable-ports-check/attempt01/state.json','c3bf8f529e151226e83d9b8db93a025f6eaf1e7d3795d2395e47ca6b731321b0','/tmp/nine-sharing-norm38-four-variable-ports-check-20261105','PASS',1),
 ('portpartial','research/nine-sharing-norm38-current-ports-split-draft/attempt01/state.json','0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4','/tmp/nine-sharing-norm38-current-ports-split-20261105','FAILED',5),
 ('currentinst','research/nine-sharing-norm38-current-four-cast-instantiation-check/attempt01/state.json','bad562eeca80d04d60ede99deb281686134612c3c091230a7326dd850b5deabf','/tmp/nine-sharing-norm38-current-four-cast-instantiation-check-20261105','PASS',1),
 ('forwardpartial','research/nine-sharing-norm38-forward-source-check/attempt01/state.json','cab44da16e5312c579738b4367e8d62b701654aff502e529a3bfd0f30744c58c','/tmp/nine-sharing-norm38-forward-source-check-20261105','FAILED',1)]
links={};selected={};counts={}
def add(rel,p):
 p=Path(p);rp=str(p.resolve());h=sha(p)
 if rel in links:need(links[rel]['sha256']==h,'overlay object conflict '+rel)
 else:links[rel]={'realpath':rp,'sha256':h}
for label,relative,pin,root,status,count in providers:
 state=D/relative;root=Path(root);need(sha(state)==pin,'provider state '+label);d=json.loads(state.read_text());need(d['status']==status,'provider status '+label);need(len(d['rows'])==count+(1 if label in ('fields','forwardpartial','sourcepartial','portpartial') else 0),'provider rows '+label)
 if label=='fields':need(d['rows'][1]['module']=='Norm38StaticCarrierConditional' and d['rows'][1]['compile']['exit']==1,'failed fields row')
 if label=='portpartial':need(d['rows'][5]['module']=='Norm38CurrentPortCasts' and d['rows'][5]['compile']['exit']==1,'failed portpartial row')
 if label=='sourcepartial':need(d['rows'][1]['module']=='Norm38CarrierUnitNorms' and d['rows'][1]['compile']['stop_reason']=='timeout','failed sourcepartial row')
 if label=='forwardpartial':need(d['rows'][1]['module']=='Norm38SourceToSeed' and d['rows'][1]['compile']['stop_reason']=='timeout','failed forward row')
 for k,v in d['overlay_links'].items():
  q=Path(k);need(q.is_symlink() and str(q.resolve())==v,'provider overlay '+k);rel=str(q.relative_to(root/'lib'));add(rel,q)
 for row in d['rows'][:count]:
  n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0 and row['compile']['stop_reason'] is None,'provider stage '+n);src=root/'src/DiophantineConsistency'/(n+'.lean');obj=root/'lib/DiophantineConsistency'/(n+'.olean');need(sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'],'provider source/object '+n)
  for phase in ('deps','compile'):need(sha(root/(n+'-'+phase+'.txt'))==row[phase]['log_sha256'],'provider log '+n)
  verify_guard(row['direct_guard']);add('DiophantineConsistency/'+n+'.olean',obj)
  if n in ('Norm38ReferenceTerminals','Norm38ReferenceFieldsAll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix','Norm38StaticToSeed','Norm38ForwardFiveNorms','Norm38FixedPortNorms','Norm38SourceCarrierZero','Norm38CurrentSourceToSeed','Norm38FourVariablePorts','Norm38CurrentFourCastInstantiation','Norm38CurrentPort0','Norm38CurrentPort1','Norm38CurrentPort2','Norm38CurrentPort3'):selected['DiophantineConsistency.'+n]={'sha256':row['object_sha256'],'realpath':str(obj.resolve())}
 counts[label]={'rows':count,'overlay_links':len(d['overlay_links'])}
need(len(selected)==15,'selected objects')
sphere=D/'research/current2011-spheres-fresh-base/attempt02/result.json';sr=Path('/tmp/current2011-spheres-fresh-base-priority-check02');need(sha(sphere)=='67159c8c4665700e59c6745b705f42ecc459ca6a38f79bd95545c8e7115c31d9'==sha(sr/'result.json'),'sphere receipt');sd=json.loads(sphere.read_text());need(sd['status']=='PASS' and sd['exit']==0 and sd['guards_stable'] and sd['guards_before']==sd['guards_after'],'sphere status');verify_guard(sd['guards_after']);need(sha(sr/'compile.log')==sd['log_sha256'] and sha(sr/'FreshCarrierSpheres.olean')==sd['object_sha256']=='37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020','sphere object/log');selected['FreshCarrierSpheres']={'sha256':sd['object_sha256'],'realpath':str((sr/'FreshCarrierSpheres.olean').resolve())}
model=D/'research/normalized106-fresh-base-model-build/attempt03/state.json';mr=Path('/tmp/normalized106-fresh-model-client-20261105');need(sha(model)=='dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23'==sha(mr/'state.json'),'model receipt');md=json.loads(model.read_text());need(md['status']=='PASS' and len(md['runs'])==2 and all(x['exit']==0 for x in md['runs']),'model status');need(sha(mr/'FreshModel106.lean')==md['source_sha256'] and sha(mr/'FreshModel106.olean')==md['object_sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','model source/object');need(sha(mr/'deps.txt')==md['runs'][0]['log_sha256'] and sha(mr/'compile.txt')==md['runs'][1]['log_sha256'],'model logs');verify_guard(md['direct_guard']);selected['FreshModel106']={'sha256':md['object_sha256'],'realpath':str((mr/'FreshModel106.olean').resolve())}
for n in ('Norm38CarrierUnitNorms','Norm38SourceToSeed','Norm38SourceFourCasts','Norm38CurrentSourceFourCasts'):need('DiophantineConsistency/'+n+'.olean' not in links,'candidate target collision '+n)
print(json.dumps({'status':'PASS_POINT_PRODUCER_SURVEY','providers':counts,'links':links,'selected':selected,'scope':'Selected source/object/log/direct-guard and overlay observations only; no Lean or complete transitive/dynamic ancestry.'},sort_keys=True))
