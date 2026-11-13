#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';P=R/'thirteen-current2011-final-checks-4g';A=P/'attempt01'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='ba9d59394f861113d27785235849c6acb582ae2e27a4047c5385c22cdb42806b'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',92068,0)
assert sha(P/'run.py')==d['runner_sha256']=='f40bc46fc15da254dae686f85ee185271a6bf732b8194b2fb98fcd9e07b7ef09'
assert sha(P/'monitor.py')=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad'
source=P/'ThirteenFinalChecks.lean';assert sha(source)=='779a7cc0745530138b39237569d6c46b929839523d21e21acee8a08a54bb8748'
assert source.read_text().strip()=='import DiophantineConsistency.ModelThirteenForms\n\n#print axioms DiophantineConsistency.ModelThirteenForms.standard_equivalence70\n#print axioms DiophantineConsistency.ModelThirteenForms.standard_equivalence71'
assert [x['exit'] for x in d['runs']]==[0,0] and d['preflight_before_sha256']==d['preflight_after_sha256']
for run,log in zip(d['runs'],['deps.txt','compile.txt']):
 assert sha(A/log)==run['log_sha256'] and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
 assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['sampling_interval_seconds']==0.1 and run['timeout_seconds']==180 and '-M4000' in run['command']
 assert run['peak_session_rss_bytes']<5*1024**3 and run['min_host_available_bytes']>=10*1024**3
log=(A/'compile.txt').read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log);assert len(reports)==2
for (name,axioms),n in zip(reports,['70','71']):assert name=='DiophantineConsistency.ModelThirteenForms.standard_equivalence'+n and [x.strip() for x in axioms.split(',')]==['propext','Classical.choice','Quot.sound']
assert d['dependencies']['DiophantineConsistency.ModelThirteenForms']['sha256']=='34445fbe3361116a892e8b5a351c2957fb4cad700179dd0b4212421f8cc7067d'
cmd=d['runs'][-1]['command'];assert sha(cmd[cmd.index('-o')+1])==d['object_sha256']=='4fdaa373449292979b912c881af2393415393730817aaea3593bf16ae52a5bfd'
assert len(d['direct_guard'])==100 and len(d['overlay_links'])==1031
for key,v in d['direct_guard'].items():
 p=pathlib.Path(key)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
print(json.dumps({'status':'PASS','outer_session':92068,'lean_exits':[0,0],'guard_slots':100,'overlay_links':1031,'axiom_reports':[n for n,_ in reports],'compile_peak_sampled_rss':d['runs'][1]['peak_session_rss_bytes'],'compile_min_available':d['runs'][1]['min_host_available_bytes'],'scope':'Standard iPRA endpoint axiom reports only; no Lean replay, GG endpoint or new base rebuild.'},indent=2))
