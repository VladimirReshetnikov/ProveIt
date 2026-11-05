#!/usr/bin/env python3
"""Read-only audit of three concrete reference topology attempts."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
packets=[('nine-sharing-norm38-reference-base-check','/tmp/nine-sharing-norm38-reference-base-check-20261105','8b341f01dc173c958a0b3e021a17f6b140deccb65dc8dab9792733ffa66e4fe9',42729,1),('nine-sharing-norm38-reference-base-retry01','/tmp/nine-sharing-norm38-reference-base-retry01-20261105','c683e8adf77e556f26790d94e14b712160b7d495e5170481fb14a3c93c9d17ea',35832,1),('nine-sharing-norm38-reference-base-retry02','/tmp/nine-sharing-norm38-reference-base-retry02-20261105','d3dc44f113f3cb6c176a67259b3d8df3c825a3ab9009f05374764ccddd7fb3ce',51506,0)]
texts=[];results=[]
for name,path,statehash,session,code in packets:
 q=R/name;a=q/'attempt01';out=Path(path);assert sha(a/'state.json')==sha(out/'state.json')==statehash;s=json.loads((a/'state.json').read_text());assert s['status']==('PASS' if code==0 else 'FAILED') and len(s['rows'])==1 and s['base_state_sha256']=='ac766e23a56ec4a7c97b8c17d4703b9d20f9081a4af0681987f7c206a7f2d2a0';r=s['rows'][0];assert r['module']=='Norm38ReferenceBase'
 source=q/'src/DiophantineConsistency/Norm38ReferenceBase.lean';text=source.read_text();texts.append(text);assert sha(source)==sha(out/'src/DiophantineConsistency/Norm38ReferenceBase.lean')==r['source_sha256']
 for typ in ('deps','compile'):
  z=r[typ];assert sha(a/('Norm38ReferenceBase-'+typ+'.txt'))==sha(out/('Norm38ReferenceBase-'+typ+'.txt'))==z['log_sha256'] and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 assert r['deps']['exit']==0 and r['compile']['exit']==code
 for p,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(p)
  else:assert Path(p).is_file() and str(Path(p).resolve())==v['realpath'] and sha(p)==v['sha256']
 for p,v in s['overlay_links'].items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
 dep=r['dependencies']['DiophantineConsistency.SharingTopology38'];assert dep['sha256']=='90661b7bf1e7be709ad2d32e67447e6e05a3d698c975a3e5632566b91fdcca38'==sha(dep['path']) and str(Path(dep['path']).resolve())==dep['realpath']
 o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==session and o['outer_exit_code']==code and 'not independently observed' in o['observation_kind']
 log=(a/'Norm38ReferenceBase-compile.txt').read_text()
 if code==0:
  assert sha(a/'Norm38ReferenceBase-compile.txt')=='832fbb4c747def34d36bbb13e9649f225f9549f2e66ee83e5b15cba75d435aff' and sha(a/'outer-terminal-author-record.json')=='08c386dabfb271c00fca46343ee789170b1831d943bd8f4f16c128bf6d9ad295'
  assert r['object_sha256']=='723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5'==sha(out/'lib/DiophantineConsistency/Norm38ReferenceBase.olean');reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log);assert len(reports)==1 and reports[0][0]=='DiophantineConsistency.Norm38Reference.graph_topological' and {x.strip() for x in reports[0][1].split(',')}=={'propext','Classical.choice','Quot.sound'} and 'sorryAx' not in log
 else:assert 'object_sha256' not in r and 'failed to synthesize' in log and 'Decidable' in log and 'sorryAx' in log
 results.append({'author_recorded_session':session,'exit':code,'state_sha256':statehash,'source_sha256':r['source_sha256'],'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links'])})
frag='theorem graph_topological : Topological NormAssignment38.gates initialNodes := by\n  decide';replacement='theorem graph_topological : Topological NormAssignment38.gates initialNodes := by\n  simp only [NormAssignment38.gates, initialNodes, Topological]\n  all_goals decide';assert texts[0].replace(frag,replacement)==texts[1]
frag='  simp only [NormAssignment38.gates, initialNodes, Topological]\n  all_goals decide';assert texts[1].replace(frag,'  simp only [NormAssignment38.gates, initialNodes, Topological]\n  repeat\' apply And.intro\n  all_goals decide')==texts[2]
prior=D/'research/nine-sharing-norm38-reference-draft';z=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(prior/'result.json').read_bytes()
print(json.dumps({'status':'PASS_CONCRETE_TOPOLOGY_TERMINAL_EVIDENCE_ONLY','attempts':results,'successful_object_sha256':'723434d993b01cc17c86d82fc0eba7bf9a7723913dc879405666631c15b265f5','success_axiom_report':['propext','Classical.choice','Quot.sound'],'scope':'Retained source/log/object and live guards; no Lean replay or independent outer-session observation.'},indent=2,sort_keys=True))
