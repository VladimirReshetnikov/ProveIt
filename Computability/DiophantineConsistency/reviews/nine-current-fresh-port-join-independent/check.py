#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
cases=[('nine-current-fresh-port-join','attempt01',36403,'FAILED',1,480,'/tmp/nine-fresh-port-join-20261105'),('nine-current-fresh-port-join-retry','attempt02',74890,'PASS',0,510,'/tmp/nine-fresh-port-join-retry-20261105')];out=[]
for name,attempt,session,status,child,slots,tmp in cases:
 P=R/name;A=P/attempt;OUT=pathlib.Path(tmp);d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());r=d['rows'][0]
 assert (d['status'],o['actual_session'],o['exit_code'],d['base_state_sha256'])==(status,session,0 if status=='PASS' else 1,'c48776fcd9993d73cead1321f41a97621967a48b66c8d18d59aa879f6b8f0888')
 assert r['module']=='NineFreshPorts' and r['source_sha256']==sha(P/'NineFreshPorts.lean')==sha(A/'source.lean')=='021f31480e76409b970e774b09d050dbdf66e9db3c1da7b8d8f4a0e102902c1b'
 for typ,ex in [('deps',0),('compile',child)]:
  x=r[typ];log=A/('NineFreshPorts-'+typ+'.txt');assert x['exit']==ex and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(log)==x['log_sha256']
  assert x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and x['sampling_interval_seconds']==0.1 and x['peak_session_rss_bytes']<4*1024**3 and x['min_host_available_bytes']>=10*1024**3
 assert len(r['direct_guard'])==slots and len(d['overlay_links'])==1056
 for k,v in r['direct_guard'].items():
  p=pathlib.Path(k)
  if v is None:assert not os.path.lexists(p),p
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
 for k,v in d['overlay_links'].items():assert pathlib.Path(k).is_symlink() and str(pathlib.Path(k).resolve())==v,k
 assert r['dependencies']['CurrentFourPortBytes']['sha256']=='9b94acd4e35406559c61c51c0822798ec56737109415a517de9f973c409daa9f' and r['dependencies']['DiophantineConsistency.IPRANineFreshCurrent']['sha256']=='3665f5e9392cc56149d1a8c3f54cc10d18dc8c3c4df828c073e8f0fd2bd459b3'
 log=(A/'NineFreshPorts-compile.txt').read_text()
 if status=='FAILED':assert "unknown module prefix 'FreshModel106'" in log and not r.get('object_sha256')
 else:
  assert ' '.join(log.split()) == "'DiophantineConsistency.NineFreshPorts.current_natural_from_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]"
  assert r['object_sha256']==sha(OUT/'lib/DiophantineConsistency/NineFreshPorts.olean')=='ac7a2bcf535e34cb2da731360372ec31d68bab0df648628980a612c6b825effd'
 out.append({'session':session,'status':status,'child_exits':[0,child],'guard_slots':slots,'overlay_links':1056,'state_sha256':sha(A/'state.json')})
P=R/'nine-current-fresh-port-join-retry';assert sha(P/'run.py')=='cb90d9887f8af5271b0353106499910d8be89d8cc9958d8dd7e6c258b5ae5c70' and sha(P/'attempt02/state.json')=='316e0b2ce1f44b54712fde4bca1b423be88fe792d025af0ab9cbe36cf200050a'
s=(P/'NineFreshPorts.lean').read_text();assert 'ObjectCurrentEquation2011.naturalExpression =\n      ObjectCurrentEquation2011.positiveShift\n        (ObjectCurrentEquation2011.expressionAt CurrentFourPortBytes.decoded)' in s and 'rw [CurrentFourPortBytes.decoded_eq_ports]\n  rfl' in s
source=(R/'nine-current-fresh-endpoint/IPRANineFreshCurrent.lean').read_text();assert 'ObjectCurrentEquation2011.naturalExpression.splitNatural.1' in source and 'ObjectCurrentEquation2011.naturalExpression.splitNatural.2' in source and 'QuarticSyntax.expression left right' in source
print(json.dumps({'status':'PASS','attempts':out,'scope':'Exact current expression equality with symbolic decoded-port tuple; no Lean gzip/filesystem theorem, no full dynamic ancestry or Lean replay.'},indent=2))
