#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';P=R/'thirteen-current2011-69-endpoints-4g';A=P/'attempt01'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='d06d30d141b4d68ad01b6e635700c7c570e6b43232eba64f77bfb35e0ea4c3a1'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',74499,0)
assert sha(P/'run.py')==d['runner_sha256']=='dedef3db90ea928df6cd0307f372651c2b2eed7a4dcb310324b1eee894cb0061'
assert sha(P/'monitor.py')=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad'
source=P/'Thirteen69Endpoints.lean';assert sha(source)=='86daa6a753c70336455ced8a2be6ac7883e478e071a3d284763e3f3448c72203';s=source.read_text()
assert s.count('(positiveShift (ModelThirteenCarrier.expressionAt69 CurrentWindowCarry2011.ports))')==2
for x in ['theorem standard_equivalence69 : IPRAStandardTheory.standardTheory ⊢','∼mappedNativeRefutation embedding','ModelThirteenCarrier.standard_equivalence69','theorem standard_translated_equivalence69 : IPRAStandardTheory.standardTheory ⊢','(Semiformula.lMap embedding sourceSentence)ᴺ','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:assert x in s,x
z=(D/'Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean').read_text();assert '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in z
assert [x['exit'] for x in d['runs']]==[0,0] and d['preflight_before_sha256']==d['preflight_after_sha256']
for run,log in zip(d['runs'],['deps.txt','compile.txt']):
 assert sha(A/log)==run['log_sha256'] and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
 assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['sampling_interval_seconds']==0.1 and run['timeout_seconds']==180 and '-M4000' in run['command']
 assert run['peak_session_rss_bytes']<5*1024**3 and run['min_host_available_bytes']>=10*1024**3
log=(A/'compile.txt').read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log);assert len(reports)==2
for (name,axioms),n in zip(reports,['standard_equivalence69','standard_translated_equivalence69']):assert name=='DiophantineConsistency.Thirteen69Endpoints.'+n and [x.strip() for x in axioms.split(',')]==['propext','Classical.choice','Quot.sound']
assert d['dependencies']['DiophantineConsistency.ModelThirteenCarrier']['sha256']=='197fb6ecbf39f9535ceb8ccafba506a2aa986e3db49f29ac5d8b8e1e3ba0ced9'
cmd=d['runs'][-1]['command'];assert sha(cmd[cmd.index('-o')+1])==d['object_sha256']=='876ed4ed0ef309ec8d22ded066e716c06c6e2321324a21a7418962367b296aaf'
assert len(d['direct_guard'])==100 and len(d['overlay_links'])==1030
for key,v in d['direct_guard'].items():
 p=pathlib.Path(key)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
print(json.dumps({'status':'PASS','outer_session':74499,'lean_exits':[0,0],'guard_slots':100,'overlay_links':1030,'axiom_reports':[n for n,_ in reports],'compile_peak_sampled_rss':d['runs'][1]['peak_session_rss_bytes'],'compile_min_available':d['runs'][1]['min_host_available_bytes'],'scope':'Standard iPRA 13/69 mapped-refutation and GG endpoints; graph counts and degree external; no Lean replay or clean base rebuild.'},indent=2))
