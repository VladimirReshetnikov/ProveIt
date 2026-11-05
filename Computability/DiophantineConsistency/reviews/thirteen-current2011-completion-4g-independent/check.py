#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';P=R/'thirteen-current2011-complete-4g-retry';A=P/'attempt03'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='c0963c19b50b76cc2e43655659ae259baeec6d0154ee3381e843ec317dc35466'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',33054,0)
assert d['runner_sha256']==sha(P/'run.py')=='347a22ac96f05a51a2e1a7ef293fbbec7d40df784a818428504f5ee6f3a37b0c'
assert sha(P/'monitor.py')=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad'
source=P/'ModelThirteenCarrier.lean';assert sha(source)=='cf7dcf8e16be4772ac39c49068425668044832303e5972e501d11c7d8536dfb1'==sha(R/'thirteen-current2011-complete-factored-attempt02/ModelThirteenCarrier.lean')
old=(R/'thirteen-current2011-carrier-split-draft/src/DiophantineConsistency/ModelThirteenCarrier.lean').read_text();new=source.read_text()
for name in ['complete','sameNoZero69','bridge69','native_equivalence69','standard_equivalence69']:
 pattern=r'(?ms)^theorem '+name+r'\b.*?\s*:='
 x=re.search(pattern,old);y=re.search(pattern,new);assert x and y and x.group()==y.group(),name
assert [x['exit'] for x in d['runs']]==[0,0] and d['preflight_before_sha256']==d['preflight_after_sha256']
for run,log in zip(d['runs'],['deps.txt','compile.txt']):
 assert sha(A/log)==run['log_sha256'] and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
 assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['sampling_interval_seconds']==0.1 and run['timeout_seconds']==180
 assert '-M4000' in run['command'] and run['peak_session_rss_bytes']<5*1024**3 and run['min_host_available_bytes']>=10*1024**3
assert (A/'compile.txt').read_bytes()==b''
cmd=d['runs'][-1]['command'];assert sha(cmd[cmd.index('-o')+1])==d['object_sha256']=='197fb6ecbf39f9535ceb8ccafba506a2aa986e3db49f29ac5d8b8e1e3ba0ced9'
assert len(d['direct_guard'])==550 and len(d['overlay_links'])==1029
for key,v in d['direct_guard'].items():
 p=pathlib.Path(key)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
want={'ModelThirteenCarrierPrelude':'918f5fc28b61155bfc417f5ce50d1a5fde0023198c1b3779937768bbb9414bff','ModelThirteenCoreInvariants':'3a4a7d8b04de145836ef2ccdfdd6cdf84cfc4c728caf5a4ec64785eb85c1a467','ModelThirteenRankOrdinate':'07fe448925823258ff75480a6bc775eb2b46566654c67906f97a8be59052b6f7','ModelThirteenNaturalSeed':'78e8605697fb3cb622288d99b50a32796027622a58f0080b890ff124c30d54c2','ModelThirteenAffineCarrier':'d362bdd5b7b7d720b5443f58612468d921e23e2c08f479f3ba6ea34340b31cf8'}
for n,h in want.items():assert d['dependencies']['DiophantineConsistency.'+n]['sha256']==h,n
print(json.dumps({'status':'PASS','outer_session':33054,'lean_exits':[0,0],'guard_slots':550,'overlay_links':1029,'compile_peak_sampled_rss':d['runs'][1]['peak_session_rss_bytes'],'compile_min_available':d['runs'][1]['min_host_available_bytes'],'scope':'Recorded 13/69 completion and standard/native bridge; no Lean replay, axiom report or adapted 70/71 endpoint.'},indent=2))
