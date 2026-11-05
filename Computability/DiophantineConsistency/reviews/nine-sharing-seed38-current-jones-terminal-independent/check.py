#!/usr/bin/env python3
"""Retained evidence audit; no Lean replay or independent outer-session witness."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=D/'research/nine-sharing-seed38-weighted-retry/attempt01/state.json';assert sha(base)=='a57517e4d934c36680f4f44524a2c8df822aa06cb8e84ec466248e2eac185534';b=json.loads(base.read_text());assert b['status']=='PASS' and len(b['rows'])==10
packets=[('client','b7c562d667c055b9a0ee71dc7fa6934170f41ec9ed7eaba2210fa3b42ed2559e',74639,1,'/tmp/nine-sharing-seed38-current-jones-20261105'),('retry01','ca43e7d3588626c70043b8909d6cbf2762784a3132d079ae22d9329485b32d1f',32288,0,'/tmp/nine-sharing-seed38-current-jones-retry01-20261105')];sources=[];stats=[]
for name,pin,session,code,out in packets:
 q=D/('research/nine-sharing-seed38-current-jones-'+name);a=q/'attempt01';assert sha(a/'state.json')==pin;d=json.loads((a/'state.json').read_text());r=d['rows'][0];src=q/'src/DiophantineConsistency/SharingSeed38CurrentJones.lean';sources.append(src.read_text());assert sha(src)==r['source_sha256'] and d['base_state_sha256']==sha(base) and len(d['overlay_links'])==1065
 receipt=json.loads((a/'outer-terminal-author-record.json').read_text());assert receipt['outer_session_id']==session and receipt['outer_exit_code']==code and 'author-recorded' in receipt['observation_kind']
 assert r['deps']['exit']==0 and r['compile']['exit']==code and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
 for phase in ('deps','compile'):assert sha(a/('SharingSeed38CurrentJones-'+phase+'.txt'))==r[phase]['log_sha256']
 assert set(r['dependencies'])=={'Init','DiophantineConsistency.SharingSeed38','DiophantineConsistency.CurrentKernelData2011'} and len(r['direct_guard'])==150
 for k,v in r['direct_guard'].items():
  path=Path(k)
  if v is None:assert not os.path.lexists(path),str(path)
  else:assert path.is_file() and str(path.resolve())==v['realpath'] and sha(path)==v['sha256'],str(path)
 for k,v in d['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
 log=(a/'SharingSeed38CurrentJones-compile.txt').read_text()
 if code:
  assert d['status']=='FAILED' and 'error: Tactic `decide` failed' in log and log.count('sorryAx')==3
 else:
  assert d['status']=='PASS' and not re.search(r'(?i)error:|warning:|sorryAx',log)
  reports=re.findall(r"depends on axioms: \[(.*?)\]",log,re.S);assert len(reports)==4 and all(re.sub(r'\s+','',x)=='propext,Classical.choice,Quot.sound' for x in reports)
  assert sha(Path(out)/'lib/DiophantineConsistency/SharingSeed38CurrentJones.olean')==r['object_sha256']=='9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e'
 stats.append({'attempt':name,'status':d['status'],'guards':len(r['direct_guard']),'overlay_links':len(d['overlay_links'])})
assert sources[0].replace('(by decide : 1 < CurrentMasks2011.radix)','(by unfold CurrentMasks2011.radix; decide : 1 < CurrentMasks2011.radix)')==sources[1]
s=sources[1];assert 'SharingSeed38.seed_degree _' in s and 'SharingSeed38.seed_normalized _ current_beta_positive 1' in s and 'NineFreshJones.nine_iff _ current_degree current_normalized' in s and 'Fin 9 → V' in s and 'Fin 38 → V' in s and 'Fin.cons (1 : V) w' in s
print(json.dumps({'status':'PASS_RETAINED_EVIDENCE_ONLY','attempts':stats,'scope':'No Lean replay or independent outer-session observation; no seed/current-equation or iPRA bridge.'},indent=2,sort_keys=True))
