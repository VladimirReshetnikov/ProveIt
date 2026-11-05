#!/usr/bin/env python3
"""Read-only audit of the three isolated slot00 proof attempts."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
packets=[('nine-sharing-norm38-slot00-probe','/tmp/nine-sharing-norm38-slot00-probe-20261105','c5ea31d3fde096cb2a7549b57052052152509eb1304f5738a31ec93dd6c58c17',70936,1),('nine-sharing-norm38-slot00-retry01','/tmp/nine-sharing-norm38-slot00-retry01-20261105','a636fed2c3453c742cebe88b31beadd230ab92f508eb360e730b507eb049c975',99410,1),('nine-sharing-norm38-slot00-retry02','/tmp/nine-sharing-norm38-slot00-retry02-20261105','dd5e25a6105e036fbe6fb5e367b58bd9426e5704ee793772f0dc1df307e93dd6',76831,0)]
original=(R/'nine-sharing-norm38-slot-extraction-draft/Norm38SlotExtraction.lean').read_text();stmt=lambda x:re.search(r'^theorem slot00\b.*? := by',x,re.S|re.M).group();target=stmt(original);reports=[];texts=[]
for name,outpath,statehash,session,exitcode in packets:
 q=R/name;a=q/'attempt01';out=Path(outpath);assert sha(a/'state.json')==sha(out/'state.json')==statehash
 s=json.loads((a/'state.json').read_text());assert len(s['rows'])==1 and s['status']==('PASS' if exitcode==0 else 'FAILED');r=s['rows'][0];assert r['module']=='Norm38SlotProbe'
 source=q/'src/DiophantineConsistency/Norm38SlotProbe.lean';text=source.read_text();texts.append(text);assert sha(source)==sha(out/'src/DiophantineConsistency/Norm38SlotProbe.lean')==r['source_sha256'] and stmt(text)==target
 for typ in ('deps','compile'):
  info=r[typ];assert sha(a/('Norm38SlotProbe-'+typ+'.txt'))==sha(out/('Norm38SlotProbe-'+typ+'.txt'))==info['log_sha256'];assert not info['monitor_errors'] and not info['observed_descendant_pids']
 assert r['deps']['exit']==0 and r['deps']['stop_reason'] is None and r['compile']['exit']==exitcode and r['compile']['stop_reason'] is None
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
 for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
 for mod,h in [('DiophantineConsistency.NormAssignment38','74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'),('DiophantineConsistency.SharingNormSquares','9b9ebd07fbfc3294bccee69a9d28c617d8999c2beaa53bf605c1e86372486762')]:assert r['dependencies'][mod]['sha256']==h and sha(r['dependencies'][mod]['path'])==h
 o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==session and o['outer_exit_code']==exitcode and 'not independently observed' in o['observation_kind']
 if exitcode==0:assert r['object_sha256']=='8cb455659834533a63352914a2d7d7ad2db302b11d67d1a30adfdc4737c45df0'==sha(out/'lib/DiophantineConsistency/Norm38SlotProbe.olean')
 else:assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency/Norm38SlotProbe.olean').exists()
 reports.append({'outer_session':session,'outer_exit':exitcode,'state_sha256':statehash,'source_sha256':r['source_sha256'],'compile_log_sha256':r['compile']['log_sha256'],'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links'])})
old='Fin.cons_succ (1 : V) w (14 : Fin 38)';new='Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (14 : Fin 38)';assert texts[0].replace(old,new)==texts[1]
old='    simpa only [] using ('+new+')';new='    have hindex : (14 : Fin 38).succ = (15 : Fin 39) := by decide\n    rw [← hindex]\n    exact '+new;assert texts[1].replace(old,new)==texts[2]
assert 'Application type mismatch' in (R/packets[0][0]/'attempt01/Norm38SlotProbe-compile.txt').read_text()
assert 'Type mismatch: After simplification' in (R/packets[1][0]/'attempt01/Norm38SlotProbe-compile.txt').read_text()
successlog=(R/packets[2][0]/'attempt01/Norm38SlotProbe-compile.txt').read_text();assert successlog.count('warning:')==5 and 'error:' not in successlog
print(json.dumps({'status':'PASS_RETAINED_SLOT00_EVIDENCE_ONLY','attempts':reports,'successful_object_sha256':'8cb455659834533a63352914a2d7d7ad2db302b11d67d1a30adfdc4737c45df0','warnings_on_success':5,'scope':'Statement text, three proof deltas, retained logs/objects and live guards; no Lean replay or independent historical outer-session observation.'},indent=2,sort_keys=True))
