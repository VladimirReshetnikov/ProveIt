#!/usr/bin/env python3
import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';Q=R/'nine-current-lightweight-endpoint-retry/attempt02/state.json'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(Q)=='00149b46384d4263ba6ddee3af1d09576735342b0bd58ac4a019438d8f1fffe6'
cases=[('nine-current-symbolic-ring-client','attempt01',14312,'FAILED',1,'e7073b3ea12f91e2905a5d9051e9b2ffbcdc103aaebef2f717315c69a9237773','b782561006719e65c501abfb72da93d7f613bcd384c9cfd65adbc789a1bad44c'),('nine-current-symbolic-ring-retry','attempt02',27853,'FAILED',-6,'a93f266473e716447b2a6330122c68d4caf738933dcbe65dc4eac1cb68199c41','153cd5b1d434288131a17c2bf5223f705246f35c7fbc97156ab4eaf2e69339fb'),('nine-current-symbolic-ring-generic','attempt03',43515,'PASS',0,'624a75bab9dd1458cef91328254805120879a079f08be04257493b927e5b5996','cbbf50192ec374b891ab1104b4eac872d7c4f07ef177ede0bf4d171861656d85')];out=[]
for name,attempt,session,status,child,srcpin,statepin in cases:
 P=R/name;A=P/attempt;d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());r=d['rows'][0]
 assert sha(A/'state.json')==statepin and (d['status'],o['actual_session'],o['exit_code'],d['base_state_sha256'])==(status,session,0 if status=='PASS' else 1,sha(Q))
 assert len(d['rows'])==1 and r['module']=='NineCurrentRing' and r['source_sha256']==srcpin==sha(P/'NineCurrentRing.lean')==sha(A/'source.lean')
 for typ,ex in [('deps',0),('compile',child)]:
  run=r[typ];log=A/('NineCurrentRing-'+typ+'.txt');assert run['exit']==ex and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids'] and sha(log)==run['log_sha256']
  assert run['rss_limit_bytes']==4*1024**3 and run['host_floor_bytes']==10*1024**3 and run['timeout_seconds']==120 and run['sampling_interval_seconds']==0.1 and run['peak_session_rss_bytes']<4*1024**3 and run['min_host_available_bytes']>=10*1024**3
 assert r['dependencies']['DiophantineConsistency.IPRANineCurrent']['sha256']=='a42b32c8876524e12fbad37bb404239c24d9d86b0c0378a3d41983fccb9b5072' and len(r['direct_guard'])==100 and len(d['overlay_links'])==1055
 for key,v in r['direct_guard'].items():
  p=pathlib.Path(key)
  if v is None:assert not os.path.lexists(p),p
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
 for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
 log=(A/'NineCurrentRing-compile.txt').read_text()
 if attempt=='attempt01':assert 'unsolved goals' in log and 'sorryAx' in log
 elif attempt=='attempt02':assert 'lean::memory_exception' in log and 'excessive memory consumption' in log
 else:
  assert log.strip()=="'DiophantineConsistency.NineCurrentRing.eval_current' depends on axioms: [propext, Classical.choice, Quot.sound]"
  assert r['object_sha256']=='1e38b96531b4845479daf78e92c2fc48da0a512c66ead4d01f690fd8ab41d93a'==sha('/tmp/nine-symbolic-ring-generic-20261105/lib/DiophantineConsistency/NineCurrentRing.olean')
 out.append({'session':session,'status':status,'child_exits':[0,child],'guard_slots':len(r['direct_guard']),'overlay_links':len(d['overlay_links']),'state_sha256':statepin})
P=R/'nine-current-symbolic-ring-generic'
assert sha(P/'EQUATION.md')=='01e82daa5daaf22e1eef67d5714ac3e34ee1f5b17453200f1b2575d7118d155c'
for n,pin in [('ExecutableJonesCore','89832bbdcfcde58747c535a12a37d9ad76d3ca3298a30c00c9b9cfe7eaff1ec4'),('JonesSyntaxCore','f79661e08bf9bc1a15a88f6c6e433542e9f7808c4dc88066b7fdac424b211384'),('ModelJonesSyntax','6237531aa559af356ce3b4bf6159c62a207037ac79fb83de937d8f89c8f1fabd')]:assert sha(D/'Lean/DiophantineConsistency'/(n+'.lean'))==pin
assert sha(P/'run.py')=='6d3586900c12ceaf8900e76e03e7afc0da49247588e144e60ed2616245b31e10';s=(P/'NineCurrentRing.lean').read_text()
for f in ['theorem eval_current {R : Type*} [CommRing R] (a : Fin 9 → R)','IPRANineCurrent.expression.evalRing a =','QuarticCompiler.witnessCount IPRANineCurrent.left IPRANineCurrent.right','let seed := IPRANineCurrent.seed','let z := indexZ seed 0','let y := indexY seed 0','let aa : Fin 10 → R := Fin.cons 1 a','∑ k ∈ codingStar ν 4','∑ i ∈ Finset.range ν','∑ i ∈ Finset.range (4 * codingLexp ν 4)','let v : RingVars R','RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (a 8) v.dvsr v.dvnd v.marg','ModelJonesSyntax.evalRing_expression','ModelJonesSyntax.mapVars_syntaxVars']:assert f in s,f
base=(D/'Lean/DiophantineConsistency/ModelJonesSyntax.lean').read_text();assert 'theorem mapVars_syntaxVars {ν : ℕ}' in base and 'theorem evalRing_expression {ν : ℕ}' in base
print(json.dumps({'status':'PASS','checks':out,'scope':'Exact symbolic evaluation in any commutative ring; no literal graph, numeric degree or Lean file theorem; no Lean replay.'},indent=2))
