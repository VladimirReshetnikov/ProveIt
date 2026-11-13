#!/usr/bin/env python3
import pathlib,json,hashlib,os
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';P=R/'thirteen-current2011-forms-4g';A=P/'attempt01'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='a7a108e579b6a18f357efacbbc5c8547831b555bfcb3507bf72d34dd8a58aa1f'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',79419,0)
assert d['runner_sha256']==sha(P/'run.py')=='871205246e00c52bb71b9a86f3d450aa9053092b3596821c525465abf3722cce'
source=P/'ModelThirteenForms.lean';assert sha(source)=='788fb1c2a31d04dc6848243423306f4d64d5b5c5069d09ea60ec584520dcb554'==sha(R/'thirteen-current2011-fresh-model/src/DiophantineConsistency/ModelThirteenForms.lean')
s=source.read_text()
historical=(D/'Lean/DiophantineConsistency/ModelThirteenForms.lean').read_text()
oldcore=(D/'Lean/DiophantineConsistency/ModelThirteenCarrier.lean').read_text()
newcore=(R/'thirteen-current2011-carrier-split-draft/src/DiophantineConsistency/ModelThirteenCarrierCore.lean').read_text()
def part(t,a,b):return t.split(a,1)[1].split(b,1)[0]
assert part(oldcore,'def front13 (p : Fin 4 → ℤ)','/-- The 13/69/174')==part(newcore,'def front13 (p : Fin 4 → ℤ)','/-- The 13/69/174')
for n,end in [(70,'/-'),(71,'\ntheorem evalRing_expressionAt70')]:assert part(historical,f'def expressionAt{n} (p : Fin 4 → ℤ)',end)==part(s,f'def expressionAt{n} (p : Fin 4 → ℤ)',end)
for n in ['70','71']:
 for x in ['def expressionAt'+n,'theorem evalRing_expressionAt'+n,'theorem sameZero'+n,'theorem bridge'+n,'theorem native_equivalence'+n,'theorem standard_equivalence'+n]:assert x in s,x
assert s.count('∼mappedNativeRefutation embedding')==4 and 'zero70_iff71 modelFacts ringPorts (fun i => ι (u i + 1))' in s and 'zero69_iff71 modelFacts ringPorts (fun i => ι (u i + 1))' in s
assert d['dependencies']['DiophantineConsistency.ModelThirteenCarrier']['sha256']=='197fb6ecbf39f9535ceb8ccafba506a2aa986e3db49f29ac5d8b8e1e3ba0ced9'
assert [x['exit'] for x in d['runs']]==[0,0] and d['preflight_before_sha256']==d['preflight_after_sha256']
for run,log in zip(d['runs'],['deps.txt','compile.txt']):
 assert sha(A/log)==run['log_sha256'] and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
 assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['sampling_interval_seconds']==0.1 and run['timeout_seconds']==180 and '-M4000' in run['command']
 assert run['peak_session_rss_bytes']<5*1024**3 and run['min_host_available_bytes']>=10*1024**3
log=(A/'compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log
cmd=d['runs'][-1]['command'];assert sha(cmd[cmd.index('-o')+1])==d['object_sha256']=='34445fbe3361116a892e8b5a351c2957fb4cad700179dd0b4212421f8cc7067d'
assert len(d['direct_guard'])==100 and len(d['overlay_links'])==1030
for key,v in d['direct_guard'].items():
 p=pathlib.Path(key)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
print(json.dumps({'status':'PASS','outer_session':79419,'lean_exits':[0,0],'guard_slots':100,'overlay_links':1030,'warning_count':log.count('warning:'),'compile_peak_sampled_rss':d['runs'][1]['peak_session_rss_bytes'],'compile_min_available':d['runs'][1]['min_host_available_bytes'],'scope':'13/70 and 13/71 expression bridges and standard/native derivations; no Lean replay or final axiom report.'},indent=2))
