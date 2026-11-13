#!/usr/bin/env python3
"""Recheck terminal artifacts and predecessor links, without running Lean."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2];p=r/'research/rational-carrier64-current14-actual-external';a=p/'observations/attempt01';o=Path('/tmp/rational-carrier64-current14-actual-external-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'RationalCarrier64ActualExternal.lean':'2be98d8369526bfca5039939ef6f9f3384a68cd7d267afac7647eb224e5e03bd',p/'check01.py':'b60a19463d05f9d32ad52cc4f7ece165e4dd58afa59e9843e2432378b9677e72',a/'result.json':'b876bd365509fe34f4234b0f23d62eb0ba63acc7124a7b4c38b389717c7d63f7',a/'compile.log':'76656fb2fdbdd287f2003867091c95ba3b0f0ab4f070790b06240e202c94a0c3',o/'RationalCarrier64ActualExternal.olean':'1486ef0d67c262527bd3cab26f6d0bfe4749fcfd8b9d068e3018c61dec1fa93c',Path('/tmp/current14-standard-fresh-build-20261104/state.json'):'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'}
prior=[(r/'research/rational-carrier64-current14-specialization/observations/attempt01/result.json','c2145d74a7879cc6644662fe2bb26fe22759570ae92a59ed6dfa037472da661f',Path('/tmp/rational-carrier64-current14-specialization-priority-check01/RationalCarrier64CurrentSpecialization.olean'),'d46386e6cec9201c5589eca2328da49144696c32252325160d7329e1b44d2d6e'),(r/'research/rational-carrier64-current14-actual-port-split/observations/beta01/result.json','3e72bfa5ba7d4ba6fe0731404d4fa7e7662777e0dd04974521df299bc206f70a',Path('/tmp/rational-carrier64-current14-beta-priority-check01/Current14BetaNonzero.olean'),'3cd491a204ca63a508e5f810010a71aa934f82c6c77d9f337d0f5ca43bd06a01')]
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
base=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_bytes())
if base['status']!='PASS' or base['source_status']!='CURRENT_AT_FINAL_CHECK':raise ValueError('base status')
for rec,rh,obj,oh in prior:
 if sha(rec)!=rh or sha(obj)!=oh:raise ValueError(('prior pin',str(rec)))
 x=json.loads(rec.read_bytes())
 if x['status']!='PASS' or x['exit']!=0 or x['stop_reason'] is not None or not x['guards_stable'] or x['object_sha256']!=oh:raise ValueError(('prior terminal',str(rec)))
x=json.loads((a/'result.json').read_bytes())
if x['status']!='PASS' or x['exit']!=0 or x['stop_reason'] is not None or not x['guards_stable'] or x['guards_before']!=x['guards_after'] or x['group_rss_samples']<1:raise ValueError('terminal')
if (a/'result.json').read_bytes()!=(o/'result.json').read_bytes() or (a/'compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('retained copies')
for f,v in x['guards_after'].items():
 f=Path(f)
 if v is None:
  if os.path.lexists(f):raise ValueError(('shadow',str(f)))
 elif not f.is_file() or str(f.resolve())!=v['realpath'] or sha(f)!=v['sha256']:raise ValueError(('guard',str(f)))
log=(a/'compile.log').read_text().strip(); reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log)
if len(reports)!=1 or reports[0][0]!='DiophantineConsistency.RationalCarrier64ActualExternal.actual_rational_zero_iff' or ' '.join(reports[0][1].split())!='propext, Classical.choice, Quot.sound':raise ValueError('axiom report')
print(json.dumps({'status':'PASS_ARTIFACT_RECHECK','guards_checked':len(x['guards_after']),'direct_predecessors':len(prior),'recorded_lean_exit':x['exit'],'object_sha256':x['object_sha256'],'scope':'Direct captured guards and predecessor receipts, no Lean replay or transitive ancestry audit.'},sort_keys=True,indent=2))
