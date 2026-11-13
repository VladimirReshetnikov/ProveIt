#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';P=R/'thirteen-current2011-translated-4g';A=P/'attempt01'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='36fc9cef1a7a032b80464e293926d010c30fc526bc2c39146623d314bf879797'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',84256,0)
assert sha(P/'run.py')==d['runner_sha256']=='58195001697e6d2140cc57d36803f50cfd3785b7de5195f7251fb039c3d19a5b'
assert sha(P/'monitor.py')=='d6d32747a34269702abd603d600a848266720aa06c0b91653942f316cd6dc1ad'
source=P/'ThirteenTranslated.lean';assert sha(source)=='13234e68158103241a8d9d2a97bf4966b98065f9e121b7d586e16c4a3114be56';s=source.read_text()
assert s.count('(Semiformula.lMap embedding sourceSentence)ᴺ')==2
assert s.count('Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)')==2
assert s.count('Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)')==2
for n in ['70','71']:
 assert 'theorem standard_translated_equivalence'+n+' : IPRAStandardTheory.standardTheory ⊢' in s
 assert '(positiveShift (ModelThirteenForms.expressionAt'+n+' CurrentWindowCarry2011.ports))' in s
 assert 'ModelThirteenForms.standard_equivalence'+n in s and '#print axioms standard_translated_equivalence'+n in s
z=(D/'Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean').read_text();assert '(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in z
f=(D/'Lean/DiophantineConsistency/FoundationZFCConsistencyNat.lean').read_text();assert 'noncomputable def sourceSentence : ArithmeticSentence :=' in f and '(LO.FirstOrder.SetTheory.ZermeloFraenkelChoice : LO.FirstOrder.SetTheory).consistent' in f
assert [x['exit'] for x in d['runs']]==[0,0] and d['preflight_before_sha256']==d['preflight_after_sha256']
for run,log in zip(d['runs'],['deps.txt','compile.txt']):
 assert sha(A/log)==run['log_sha256'] and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
 assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['sampling_interval_seconds']==0.1 and run['timeout_seconds']==180 and '-M4000' in run['command']
 assert run['peak_session_rss_bytes']<5*1024**3 and run['min_host_available_bytes']>=10*1024**3
log=(A/'compile.txt').read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log);assert len(reports)==2
for (name,axioms),n in zip(reports,['70','71']):assert name=='DiophantineConsistency.ThirteenTranslated.standard_translated_equivalence'+n and [x.strip() for x in axioms.split(',')]==['propext','Classical.choice','Quot.sound']
assert d['dependencies']['DiophantineConsistency.ModelThirteenForms']['sha256']=='34445fbe3361116a892e8b5a351c2957fb4cad700179dd0b4212421f8cc7067d'
cmd=d['runs'][-1]['command'];assert sha(cmd[cmd.index('-o')+1])==d['object_sha256']=='91f0f508a71fcc2a490414dac0b79602a6a23999d6fcc8585c49f46f91c726a7'
assert len(d['direct_guard'])==100 and len(d['overlay_links'])==1031
for key,v in d['direct_guard'].items():
 p=pathlib.Path(key)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
print(json.dumps({'status':'PASS','outer_session':84256,'lean_exits':[0,0],'guard_slots':100,'overlay_links':1031,'axiom_reports':[n for n,_ in reports],'compile_peak_sampled_rss':d['runs'][1]['peak_session_rss_bytes'],'compile_min_available':d['runs'][1]['min_host_available_bytes'],'scope':'Standard iPRA mapped GG translated consistency endpoints; counts and degrees external; no Lean replay or clean base rebuild.'},indent=2))
