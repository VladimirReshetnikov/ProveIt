#!/usr/bin/env python3
"""Read-only audit of each-slot first failure and successful retry."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
packets=[('nine-sharing-norm38-each-slot-check','/tmp/nine-sharing-norm38-each-slot-check-20261105','8d0a9a33484138c7ae8ccb9e91641a6d5fa2d6da54f23388c01a8b078973cbb4',12176,1),('nine-sharing-norm38-each-slot-retry01','/tmp/nine-sharing-norm38-each-slot-retry01-20261105','8bd674fad57bcb8dfe1d4d98dc8ba5716be15bc7d9c029f39198e53557bdfa70',32937,0)]
orig=(R/'nine-sharing-norm38-slot-extraction-draft/Norm38SlotExtraction.lean').read_text();stmt=lambda x:re.search(r'^theorem each_slot_zero\b.*? := by',x,re.S|re.M).group();target=stmt(orig);texts=[];result=[]
for name,path,h,session,code in packets:
 q=R/name;a=q/'attempt01';out=Path(path);assert sha(a/'state.json')==sha(out/'state.json')==h;s=json.loads((a/'state.json').read_text());assert s['status']==('PASS' if code==0 else 'FAILED') and len(s['rows'])==1
 r=s['rows'][0];assert r['module']=='Norm38EachSlot';src=q/'src/DiophantineConsistency/Norm38EachSlot.lean';text=src.read_text();texts.append(text);assert stmt(text)==target and sha(src)==sha(out/'src/DiophantineConsistency/Norm38EachSlot.lean')==r['source_sha256']
 for typ in ('deps','compile'):
  m=r[typ];assert sha(a/('Norm38EachSlot-'+typ+'.txt'))==sha(out/('Norm38EachSlot-'+typ+'.txt'))==m['log_sha256'];assert m['stop_reason'] is None and not m['monitor_errors'] and not m['observed_descendant_pids']
 assert r['deps']['exit']==0 and r['compile']['exit']==code
 dep=r['dependencies']['DiophantineConsistency.Norm38SlotsBase'];assert dep['sha256']=='5fc858cf2ab5b9a2bff40f2ef861be2d4276cdbd91c88588d5a47fd0e414d967'==sha(dep['path']) and str(Path(dep['path']).resolve())==dep['realpath']
 for p,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(p)
  else:assert Path(p).is_file() and str(Path(p).resolve())==v['realpath'] and sha(p)==v['sha256']
 for p,v in s['overlay_links'].items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
 o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==session and o['outer_exit_code']==code and 'not independently observed' in o['observation_kind']
 if code==0:
  assert r['object_sha256']=='2e3d38650deab38173769dc3a5e75e0c4ce992d647868bab04ac74c8855879da'==sha(out/'lib/DiophantineConsistency/Norm38EachSlot.olean');assert (a/'Norm38EachSlot-compile.txt').read_bytes()==b''
 else:assert 'object_sha256' not in r and 'internalZero_iff.mp`' in (a/'Norm38EachSlot-compile.txt').read_text()
 result.append({'author_recorded_session':session,'outer_exit':code,'state_sha256':h,'source_sha256':r['source_sha256'],'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links'])})
assert texts[0].count('internalZero_iff.mp (all _ hm)')==1 and texts[0].replace('internalZero_iff.mp (all _ hm)','(internalZero_iff _ _).mp (all _ hm)')==texts[1]
print(json.dumps({'status':'PASS_RETAINED_EACH_SLOT_EVIDENCE_ONLY','attempts':result,'successful_object_sha256':'2e3d38650deab38173769dc3a5e75e0c4ce992d647868bab04ac74c8855879da','scope':'Retained source, logs, object and point-in-time direct guards; no Lean replay or independent historical outer exit.'},indent=2,sort_keys=True))
