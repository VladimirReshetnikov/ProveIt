#!/usr/bin/env python3
"""Read-only terminal and direct-producer audit of two reference fields."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];q=D/'research/nine-sharing-norm38-reference-fields01-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-fields01-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='395733ddb717547637718bdc8914a86e94d19e2798148c3d7bf4b4df73c9b292';assert sha(a/'Norm38ReferenceFields01-compile.txt')=='001dfc803d7deb2c69966009d622bae533f6e7d08f6d113721fe3817325a8f22';assert sha(a/'outer-terminal-author-record.json')=='0a0991801a927d8f08b8e996c49b6fef666e42f6a77bf10d22482d0e05f4ad5e'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['base_state_sha256']=='d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce';r=s['rows'][0];assert r['module']=='Norm38ReferenceFields01'
src=q/'src/DiophantineConsistency/Norm38ReferenceFields01.lean';assert sha(src)==sha(out/'src/DiophantineConsistency/Norm38ReferenceFields01.lean')==r['source_sha256']=='5e7180f796e3b3dd420b885e0a97892638516920b0d8bdda30a796ab88d3f4e6';text=src.read_text();assert 'reference p x 61 = (Carrier65.core p x).P' in text and 'reference p x 44 = (Carrier65.core p x).Q' in text and text.count('[CommRing R]')==2
obj=out/'lib/DiophantineConsistency/Norm38ReferenceFields01.olean';assert sha(obj)==r['object_sha256']=='032511edc32be5e4e4cf9ee6a3a610ce0220a71a634b8f345615263b43c17fce'
for typ in ('deps','compile'):
 z=r[typ];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/('Norm38ReferenceFields01-'+typ+'.txt'))==sha(out/('Norm38ReferenceFields01-'+typ+'.txt'))==z['log_sha256']
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:assert Path(path).is_file() and str(Path(path).resolve())==v['realpath'] and sha(path)==v['sha256']
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for name,h in [('DiophantineConsistency.Norm38ReferenceBase','723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5'),('DiophantineConsistency.Carrier65','10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f')]:
 dep=r['dependencies'][name];assert dep['sha256']==sha(dep['path'])==h and str(Path(dep['path']).resolve())==dep['realpath']
z=subprocess.run([sys.executable,'-I','-S','-B',str(q/'carrier_preflight.py')],capture_output=True);assert z.returncode==0 and not z.stderr and json.loads(z.stdout)['status']=='PASS_POINT_IN_TIME_CARRIER_PROVIDER'
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",(a/'Norm38ReferenceFields01-compile.txt').read_text());assert len(reports)==2
assert reports[0][0]=='DiophantineConsistency.Norm38Reference.reference_P' and {x.strip() for x in reports[0][1].split(',')}=={'propext','Quot.sound'}
assert reports[1][0]=='DiophantineConsistency.Norm38Reference.reference_Q' and {x.strip() for x in reports[1][1].split(',')}=={'propext'}
assert (a/'Norm38ReferenceFields01-compile.txt').read_text().count('warning:')==2
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==89798 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
print(json.dumps({'status':'PASS_REFERENCE_PQ_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':sha(obj),'author_recorded_outer_session':89798,'author_recorded_exit':0,'axiom_reports':reports,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Retained result and current selected-producer survey; no Lean replay or independent historical exit.'},indent=2,sort_keys=True))
