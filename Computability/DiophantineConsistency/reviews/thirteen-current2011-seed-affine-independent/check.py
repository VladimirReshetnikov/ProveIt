#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
cases=[('natural-seed-draft/attempt01',98597,1,'FAILED',1,'absdiff'),('natural-seed-attempt02/attempt02',49737,0,'PASS',0,None),('affine-carrier-draft/attempt01',86952,1,'FAILED',1,'modelFacts'),('affine-carrier-attempt02/attempt02',68312,0,'PASS',0,None)];out=[]
for n,session,outer,status,exit,missing in cases:
 p=R/('thirteen-current2011-'+n);d=json.loads((p/'state.json').read_text());o=json.loads((p/'outer-terminal.json').read_text());assert (d['status'],o['actual_session'],o['exit_code'])==(status,session,outer)
 assert [r['exit'] for r in d['runs']]==[0,exit]
 for r,f in zip(d['runs'],['deps.txt','compile.txt']):assert sha(p/f)==r['log_sha256']
 log=(p/'compile.txt').read_text()
 if status=='PASS':
  assert d['preflight_before_sha256']==d['preflight_after_sha256'];cmd=d['runs'][-1]['command'];assert sha(cmd[cmd.index('-o')+1])==d['object_sha256']
  assert 'sorryAx' not in log and len(re.findall(r'depends on axioms: \[\s*propext,\s*Classical.choice,\s*Quot.sound\s*\]',log))==1
 else:assert 'Unknown identifier `'+missing+'`' in log and 'sorryAx' in log
 for key,v in d['direct_guard'].items():
  q=pathlib.Path(key)
  if v is None:assert not os.path.lexists(q),q
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256'],q
 for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
 out.append({'packet':n,'outer_session':session,'outer_exit':outer,'compile_exit':exit,'guard_slots':len(d['direct_guard']),'overlay_links':len(d['overlay_links']),'state_sha256':sha(p/'state.json')})
A=R/'thirteen-current2011-natural-seed-draft/ModelThirteenNaturalSeed.lean';B=R/'thirteen-current2011-natural-seed-attempt02/ModelThirteenNaturalSeed.lean';C=R/'thirteen-current2011-affine-carrier-draft/ModelThirteenAffineCarrier.lean';E=R/'thirteen-current2011-affine-carrier-attempt02/ModelThirteenAffineCarrier.lean'
a,b,c,e=[p.read_text() for p in [A,B,C,E]]
assert a.replace('open ArithmeticPellRecurrence\n','open ArithmeticPellRecurrence ArithmeticPellHalfIndex\n')==b
assert c.replace('open ModelDifferenceRing DiscreteOrderedRingFacts\n','open ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres\n')==e
assert sha(B)=='818258c51d3477637a04f4fcb55c9803d4bc0810617c07fde311e37f69b89583' and sha(E)=='eea57a6e0eaf7d8bc58bcd3e0756a719ff26b35782f164af0ce33a3baf10138e'
for f in ['(hb : 0 < b) (hc : 0 < c)','(hphase : R % 4 = 3) (hcR : c = ycoord R a)','ArithmeticThirteenSeed.strong_index','ArithmeticThirteenSeed.auxiliary_seed_of']:assert f in b
for f in ['(hb : 0 < b) (hG : 0 < G) (hGb : G = ι b * g)','(he4 : y + 1 = 4 * b * e4)','(hsmall : |-(ι y : DiffRing V)| < 2 * |(ι u : DiffRing V)|)','ModelThirteenRestoration.affine_carrier_pos modelFacts']:assert f in e
print(json.dumps({'status':'PASS','checks':out,'scope':'Conditional helper lemmas and namespace-only failed variants; no Lean replay or completion claim.'},indent=2))
