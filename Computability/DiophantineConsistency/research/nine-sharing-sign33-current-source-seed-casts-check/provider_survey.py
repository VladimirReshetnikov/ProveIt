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
 ('batch00','research/nine-sharing-sign33-residual-batch00-check/attempt01/state.json','580b48eb8714eb4ee78ac24d87c4114fb0ce368ec1b625978480dd7be6f1f1a7','/tmp/nine-sharing-sign33-residual-batch00-check-20261106','PASS',1),
 ('batch01','research/nine-sharing-sign33-residual-batch01-check/attempt01/state.json','6170430d297f93910f6ea89f35d0994308ea9968f8d25f903d990519859e4773','/tmp/nine-sharing-sign33-residual-batch01-check-20261106','PASS',1),
 ('batch02','research/nine-sharing-sign33-residual-batch02-check/attempt01/state.json','e73c186d80a98879177d8867b9328406a50b0b10b5d200ec012046443ec20c98','/tmp/nine-sharing-sign33-residual-batch02-check-20261106','PASS',1),
 ('batch03','research/nine-sharing-sign33-residual-batch03-check/attempt01/state.json','5162fbb298874db8f114ee3bd5b2c18756690f86272f6ff0ef6d48db3551d599','/tmp/nine-sharing-sign33-residual-batch03-check-20261106','PASS',1),
 ('batch04','research/nine-sharing-sign33-residual-batch04-check/attempt01/state.json','c5bf9844cfb813dcabdcadde7438970c97d72bfd37d3081da668f0356a67fa67','/tmp/nine-sharing-sign33-residual-batch04-check-20261106','PASS',1),
 ('batch05','research/nine-sharing-sign33-residual-batch05-check/attempt01/state.json','659fd8325cf95592f6e143d6a8af47225d62c760b243835c62279ea7083786f1','/tmp/nine-sharing-sign33-residual-batch05-check-20261106','PASS',1),
 ('batch06','research/nine-sharing-sign33-residual-batch06-check/attempt01/state.json','38aab91c79cf582e9c8910eb4998dd6ce6bfa72ff729de468e1061c5b019dc8e','/tmp/nine-sharing-sign33-residual-batch06-check-20261106','PASS',1),
 ('batch07','research/nine-sharing-sign33-residual-batch07-check/attempt01/state.json','cb55da080e2fec69cb082e9deaa5d9e6f03dfbd106e9fa22107cc3626d7fd69c','/tmp/nine-sharing-sign33-residual-batch07-check-20261106','PASS',1),
 ('assembly','research/nine-sharing-sign33-residual-assembly-check/attempt01/state.json','689fe69a26c9315785321d7fa1fcf37472fb42380540860e201d94ac98762ca9','/tmp/nine-sharing-sign33-residual-assembly-check-20261106','PASS',1),
 ('converse','research/nine-sharing-sign33-residual-converse-check/attempt01/state.json','d462e47723cb4ecee4963517244d1eb0ec23d532ca772795eea35a8a3633cd8c','/tmp/nine-sharing-sign33-residual-converse-check-20261106','PASS',9),
 ('weighted','research/nine-sharing-seed38-weighted-retry/attempt01/state.json','a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534','/tmp/nine-sharing-seed38-weighted-retry-20261105','PASS',10),
 ('lift','research/nine-sharing-sign33-lift38-check/attempt01/state.json','98e91e8236694a2e6531268547b2f6ef45cd0dec2213e06bdf535e2b27d8ebd0','/tmp/nine-sharing-sign33-lift38-check-20261106','PASS',1),
 ('forward33','research/nine-sharing-sign33-forward-constructor-check/attempt01/state.json','90d2364c1d5193dc53a3afac3ed108e23db42b2917f9e8740fee1f81b86c11ed','/tmp/nine-sharing-sign33-forward-constructor-check-20261106','PASS',1),
 ('abstract22','research/nine-sharing-sign33-abstract-projection22-check/attempt01/state.json','2464c7f1a7f03d85770c354c5dbb5130c51edf6fdce392e297732373b0cdb8eb','/tmp/nine-sharing-sign33-abstract-projection22-check-20261106','PASS',2),
 ('abstract2832','research/nine-sharing-sign33-abstract-projections28-32-check/attempt01/state.json','db2eaf9f695f596451f3cefa87f5051b4c2bf56d32c7e43d3c8279c79b0e5932','/tmp/nine-sharing-sign33-abstract-projections28-32-check-20261106','PASS',2),
 ('negative76','research/nine-sharing-sign33-negative-node76-retry01/attempt01/state.json','80883e2565238e882f9a9dd3773313888bdee7b5d8921ccf6497c6e406bba13c','/tmp/nine-sharing-sign33-negative-node76-retry01-20261106','PASS',1),
 ('node78factor','research/nine-sharing-sign33-node78-factor-check/attempt01/state.json','c59906a32aa1a905544c2bac4b791f4fa76d7bc179fd8ba1ccb83feb9a4261c3','/tmp/nine-sharing-sign33-node78-factor-check-20261106','PASS',1),
 ('fw00','research/nine-sharing-sign33-forward-group00-check/attempt01/state.json','670a12d60b02d3c6e9e2021ee9661e5edf5fefd3c09d96c4b9d1758b48804acd','/tmp/nine-sharing-sign33-forward-group00-check-20261106','PASS',1),
 ('fw01','research/nine-sharing-sign33-forward-group01-check/attempt01/state.json','d3aedeb8261f059ff714def42a7dc56dedf1630c29b9d145832ee7b83ddbe7d2','/tmp/nine-sharing-sign33-forward-group01-check-20261106','PASS',1),
 ('fw02','research/nine-sharing-sign33-forward-group02-check/attempt01/state.json','d1ec4a373141b7dd06a7be11975c66d395ceb4c8146e5da4562cb6bd2297c0bd','/tmp/nine-sharing-sign33-forward-group02-check-20261106','PASS',1),
 ('fw03','research/nine-sharing-sign33-forward-group03-positive-check/attempt01/state.json','27cde04c2415fc6d5728da8430b2ee55f140dfb200440fa26bbd796c3ce68152','/tmp/nine-sharing-sign33-forward-group03-positive-check-20261106','PASS',1),
 ('fw04','research/nine-sharing-sign33-forward-late-positive-check/attempt01/state.json','07b8243a8bb46e1165707e80fc149a90bc8c12b30de6b5ba38f5b68d361fbec7','/tmp/nine-sharing-sign33-forward-late-positive-check-20261106','PASS',1),
 ('fw05','research/nine-sharing-sign33-forward-gap-check/attempt01/state.json','f14fcd947acbf345ee0a7cac667d6168794bc830a7ee5870f33e3a7b486a94b9','/tmp/nine-sharing-sign33-forward-gap-check-20261106','PASS',1),
 ('fw06','research/nine-sharing-sign33-forward-tau-check/attempt01/state.json','913c8470a312493bd43070afb23a57c7e1e4c6cc36c325f8a09c3fcb335edc71','/tmp/nine-sharing-sign33-forward-tau-check-20261106','PASS',1),
 ('fw07','research/nine-sharing-sign33-forward-inner-check/attempt01/state.json','e21f1ef801c65a111bbf1a360cdff6c1bf003cbf6ce529a925c57fd270ad2d8a','/tmp/nine-sharing-sign33-forward-inner-check-20261106','PASS',1),
 ('fw08','research/nine-sharing-sign33-forward-value-negative-retry01/attempt01/state.json','6a0a5b963330ade28c199869910227980747a6f8f7b16420242de5744d6141bb','/tmp/nine-sharing-sign33-forward-value-negative-retry01-20261106','PASS',1),
 ('fw09','research/nine-sharing-sign33-forward-norm-q-retry02/attempt01/state.json','39dde1f529c3b65a07bfa40dd21a003711d673d1191df4e75b8945261533a26f','/tmp/nine-sharing-sign33-forward-norm-q-retry02-20261106','PASS',2),
 ('fw10','research/nine-sharing-sign33-forward-norm-w-check/attempt01/state.json','bf89cd99fe0a8f85192fbe2ad20f241c078794189a444654c4b174df34d2a3b7','/tmp/nine-sharing-sign33-forward-norm-w-check-20261106','PASS',2),
 ('fw11','research/nine-sharing-sign33-forward-norm-p-retry02/attempt01/state.json','04830736f5a36388f9daafe92232587f8baec4b265db021ce256b5a15a8adffa','/tmp/nine-sharing-sign33-forward-norm-p-retry02-20261106','PASS',1),
 ('fw12','research/nine-sharing-sign33-forward-norm-strong-retry02/attempt01/state.json','8ff5f481078daae9259ee3f9f7180e8c567a1d8c76c7fd5ef0d1e379e773a5ad','/tmp/nine-sharing-sign33-forward-norm-strong-retry02-20261106','PASS',2),
 ('fw13','research/nine-sharing-sign33-forward-norm-u-check/attempt01/state.json','38684d452247c485eea2dade759bc7563f7ac85f04b7e9e0ec0c4b584a3d0b63','/tmp/nine-sharing-sign33-forward-norm-u-check-20261106','PASS',2),
 ('corecuts','research/nine-sharing-sign33-current-core-cuts-retry01/attempt01/state.json','7df5e65c8c86be59c6af3f79b2ea99caf493907ea28a4c711efd1d83c679d8e9','/tmp/nine-sharing-sign33-current-core-cuts-retry01-20261106','PASS',1),
 ('naturalenorms','research/nine-sharing-sign33-current-natural-core-norms-check/attempt01/state.json','f0d666474d850def450411c2007eb2d8d57329709b5450aee08a501004fef086','/tmp/nine-sharing-sign33-current-natural-core-norms-check-20261106','PASS',1),
 ('allcuts','research/nine-sharing-sign33-forward-all-cuts-check/attempt01/state.json','9df2673dfbe6180174f1768b1fafea8b2b8400e6f509ba2ab648947854b7f0f9','/tmp/nine-sharing-sign33-forward-all-cuts-check-20261106','PASS',1),
 ('sourceallcuts','research/nine-sharing-sign33-current-forward-all-cuts-check/attempt01/state.json','a2a847e5f153f20fc29faaf3b19ffe4c8730f99b608f42be21ac05c95f751109','/tmp/nine-sharing-sign33-current-forward-all-cuts-check-20261106','PASS',1),
 ('residualiff','research/nine-sharing-sign33-residual-iff-check/attempt01/state.json','675b8c15e4f4e084ba650bc49590384612292c45b1f2cbc345a72e5ae399a36b','/tmp/nine-sharing-sign33-residual-iff-check-20261106','PASS',1),
 ('sourceseed','research/nine-sharing-sign33-current-source-seed-check/attempt01/state.json','2d3716f0525be2264e28ad8b6715342a4fa29bf8de6130520d2c5dfc8a1fdbe7','/tmp/nine-sharing-sign33-current-source-seed-check-20261106','PASS',1),
 ('fourvariable','research/nine-sharing-norm38-four-variable-ports-check/attempt01/state.json','c3bf8f529e151226e83d9b8db93a025f6eaf1e7d3795d2395e47ca6b731321b0','/tmp/nine-sharing-norm38-four-variable-ports-check-20261105','PASS',1),
 ('portsplit','research/nine-sharing-norm38-current-ports-split-draft/attempt01/state.json','0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4','/tmp/nine-sharing-norm38-current-ports-split-20261105','FAILED',5),
 ('forwardpartial','research/nine-sharing-norm38-forward-source-check/attempt01/state.json','cab44da16e5312c579738b4367e8d62b701654aff502e529a3bfd0f30744c58c','/tmp/nine-sharing-norm38-forward-source-check-20261105','FAILED',1)]
links={};selected={};counts={}
def add(rel,p):
 p=Path(p);rp=str(p.resolve());h=sha(p)
 if rel in links:need(links[rel]['sha256']==h,'overlay object conflict '+rel)
 else:links[rel]={'realpath':rp,'sha256':h}
for label,relative,pin,root,status,count in providers:
 state=D/relative;root=Path(root);need(sha(state)==pin,'provider state '+label);d=json.loads(state.read_text());need(d['status']==status,'provider status '+label);need(len(d['rows'])==count+(1 if label in ('fields','forwardpartial','sourcepartial','portsplit') else 0),'provider rows '+label)
 if label=='portsplit':need(d['rows'][5]['module']=='Norm38CurrentPortCasts' and d['rows'][5]['compile']['exit']==1,'failed port assembly row')
 if label=='fields':need(d['rows'][1]['module']=='Norm38StaticCarrierConditional' and d['rows'][1]['compile']['exit']==1,'failed fields row')
 if label=='sourcepartial':need(d['rows'][1]['module']=='Norm38CarrierUnitNorms' and d['rows'][1]['compile']['stop_reason']=='timeout','failed sourcepartial row')
 if label=='forwardpartial':need(d['rows'][1]['module']=='Norm38SourceToSeed' and d['rows'][1]['compile']['stop_reason']=='timeout','failed forward row')
 for k,v in d['overlay_links'].items():
  q=Path(k);need(q.is_symlink() and str(q.resolve())==v,'provider overlay '+k);rel=str(q.relative_to(root/'lib'));add(rel,q)
 for row in d['rows'][:count]:
  n=row['module'];need(row['deps']['exit']==0 and row['compile']['exit']==0 and row['compile']['stop_reason'] is None,'provider stage '+n);src=root/'src/DiophantineConsistency'/(n+'.lean');obj=root/'lib/DiophantineConsistency'/(n+'.olean');need(sha(src)==row['source_sha256'] and sha(obj)==row['object_sha256'],'provider source/object '+n)
  for phase in ('deps','compile'):need(sha(root/(n+'-'+phase+'.txt'))==row[phase]['log_sha256'],'provider log '+n)
  verify_guard(row['direct_guard']);add('DiophantineConsistency/'+n+'.olean',obj)
  if n in ('Norm38ReferenceTerminals','Norm38ReferenceFieldsAll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix','Norm38StaticToSeed','Norm38ForwardFiveNorms','Norm38FixedPortNorms','Norm38SourceCarrierZero','Norm38CurrentCastFreeIff','Sign33Windows','Sign33StrongF','Sign33AbsDiffSquare','Sign33GapTauRing','Sign33InnerVRing','Sign33AuxRing','Sign33CurrentWindows','Sign33FiveWitnesses','SharingSign33Squares','Sign33FirstCut','Sign33ResidualBatch00','Sign33ResidualBatch01','Sign33ResidualBatch02','Sign33ResidualBatch03','Sign33ResidualBatch04','Sign33ResidualBatch05','Sign33ResidualBatch06','Sign33ResidualBatch07','Sign33ResidualAssembly','Sign33ResidualConverse','NormAssignment38','Sign33Lift38','ForwardWitness38','SharingForward33','Sign33AbstractTuple','Sign33AbstractProjection22','Sign33AbstractProjection28','Sign33AbstractProjection32','Sign33NegativeNode76','Sign33Node78Factor','Sign33ForwardGroup00','Sign33ForwardGroup01','Sign33ForwardGroup02','Sign33ForwardGroup03Positive','Sign33ForwardLatePositive','Sign33ForwardGap','Sign33ForwardTau','Sign33ForwardInner','Sign33ForwardValueNegative','Sign33ForwardNormQ38','Sign33ForwardNormQRetry','Sign33ForwardNormW38','Sign33ForwardNormW','Sign33ForwardNormP','Sign33ForwardNormStrong38','Sign33ForwardNormStrong','Sign33ForwardNormU38','Sign33ForwardNormU','Sign33CurrentCoreCuts','Sign33CurrentNaturalCoreNorms','Sign33ForwardAllCuts','Sign33CurrentForwardAllCuts','Sign33ResidualIff','Sign33CurrentSourceSeed','Norm38FourVariablePorts','Norm38CurrentPort0','Norm38CurrentPort1','Norm38CurrentPort2','Norm38CurrentPort3'):selected['DiophantineConsistency.'+n]={'sha256':row['object_sha256'],'realpath':str(obj.resolve())}
 counts[label]={'rows':count,'overlay_links':len(d['overlay_links'])}
need(len(selected)==68,'selected objects')
sphere=D/'research/current2011-spheres-fresh-base/attempt02/result.json';sr=Path('/tmp/current2011-spheres-fresh-base-priority-check02');need(sha(sphere)=='67159c8c4665700e59c6745b705f42ecc459ca6a38f79bd95545c8e7115c31d9'==sha(sr/'result.json'),'sphere receipt');sd=json.loads(sphere.read_text());need(sd['status']=='PASS' and sd['exit']==0 and sd['guards_stable'] and sd['guards_before']==sd['guards_after'],'sphere status');verify_guard(sd['guards_after']);need(sha(sr/'compile.log')==sd['log_sha256'] and sha(sr/'FreshCarrierSpheres.olean')==sd['object_sha256']=='37d9d82deafedceec4ec73146c6ec0cdfe0896b36d5a86f4182158d3f7f82020','sphere object/log');selected['FreshCarrierSpheres']={'sha256':sd['object_sha256'],'realpath':str((sr/'FreshCarrierSpheres.olean').resolve())}
model=D/'research/normalized106-fresh-base-model-build/attempt03/state.json';mr=Path('/tmp/normalized106-fresh-model-client-20261105');need(sha(model)=='dea372080bd6380703bdf770bde887436699f7998e7927dacadb2bec66016d23'==sha(mr/'state.json'),'model receipt');md=json.loads(model.read_text());need(md['status']=='PASS' and len(md['runs'])==2 and all(x['exit']==0 for x in md['runs']),'model status');need(sha(mr/'FreshModel106.lean')==md['source_sha256'] and sha(mr/'FreshModel106.olean')==md['object_sha256']=='d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942','model source/object');need(sha(mr/'deps.txt')==md['runs'][0]['log_sha256'] and sha(mr/'compile.txt')==md['runs'][1]['log_sha256'],'model logs');verify_guard(md['direct_guard']);selected['FreshModel106']={'sha256':md['object_sha256'],'realpath':str((mr/'FreshModel106.olean').resolve())}
for n in ('Norm38CarrierUnitNorms','Norm38SourceToSeed','Sign33SourceSeedFourCasts','Sign33CurrentSourceSeedCastFree'):need('DiophantineConsistency/'+n+'.olean' not in links,'candidate target collision '+n)
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
