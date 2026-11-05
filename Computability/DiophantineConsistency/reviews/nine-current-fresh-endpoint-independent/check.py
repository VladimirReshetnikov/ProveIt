#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
PKT='nine-current-fresh-endpoint'
TMP='/tmp/nine-fresh-endpoint-20261105'
STATE='c48776fcd9993d73cead1321f41a97621967a48b66c8d18d59aa879f6b8f0888'
SESSION=65720
BASE='469b279c32677e416e757dcd59835ea0514d1e524338d3c451ae8cfa8e446439'
RUNNER='89da54f2aa9f3ce81eff8e3e56875fb0135a488e3802e055bfa896a026fb7c33'
MOD='IPRANineFreshCurrent'
SOURCE='2a6db17518f909026efe5039e13d151dc690e83458edd0762396c9304d001281'
OBJ='3665f5e9392cc56149d1a8c3f54cc10d18dc8c3c4df828c073e8f0fd2bd459b3'
GUARDS=250
LINKS=1055
REPORTS=['DiophantineConsistency.NineFreshJones.jonesModel', 'DiophantineConsistency.IPRANineFreshCurrent.polynomialBridge', 'DiophantineConsistency.IPRANineFreshCurrent.native_equivalence', 'DiophantineConsistency.IPRANineFreshCurrent.standard_equivalence', 'DiophantineConsistency.IPRANineFreshCurrent.standard_translated_equivalence']
SCOPE='Unique-namespace natural-nine-variable abstract endpoint; no literal graph or degree.'
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';P=R/PKT;A=P/'attempt01';OUT=pathlib.Path(TMP)
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')==STATE and (d['status'],o['actual_session'],o['exit_code'],d['base_state_sha256'])==('PASS',SESSION,0,BASE)
assert sha(P/'run.py')==d['runner_sha256']==RUNNER and len(d['rows'])==1;r=d['rows'][0];assert r['module']==MOD and r['source_sha256']==SOURCE==sha(P/(MOD+'.lean'))==sha(OUT/'src/DiophantineConsistency'/(MOD+'.lean'))
for typ in ['deps','compile']:
 x=r[typ];log=A/(MOD+'-'+typ+'.txt');assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(log)==x['log_sha256']
 assert x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and x['sampling_interval_seconds']==0.1 and x['peak_session_rss_bytes']<4*1024**3 and x['min_host_available_bytes']>=10*1024**3
assert r['object_sha256']==OBJ==sha(OUT/'lib/DiophantineConsistency'/(MOD+'.olean')) and len(r['direct_guard'])==GUARDS and len(d['overlay_links'])==LINKS
for k,v in r['direct_guard'].items():
 p=pathlib.Path(k)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for k,v in d['overlay_links'].items():assert pathlib.Path(k).is_symlink() and str(pathlib.Path(k).resolve())==v,k
log=(A/(MOD+'-compile.txt')).read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log);assert [x[0] for x in reports]==REPORTS and all([x.strip() for x in a.split(',')]==['propext','Classical.choice','Quot.sound'] for _,a in reports);assert 'sorryAx' not in log and 'error:' not in log
s=(P/'IPRANineFreshCurrent.lean').read_text()
old=(R/'nine-current-lightweight-endpoint-retry/IPRANineCurrent.lean').read_text().replace('ModelJonesNine.jonesModel','NineFreshJones.jonesModel').replace('IPRANineCurrent','IPRANineFreshCurrent')
for name in ['source_iff','zero_iff_current','polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence']:
 pattern=r'(?ms)^theorem '+name+r'\b.*?(?=^theorem |^end Model|^#print|^end DiophantineConsistency)';x=re.search(pattern,old);y=re.search(pattern,s);assert x and y and x.group()==y.group(),name
assert r['dependencies']['DiophantineConsistency.NineFreshJones']['sha256']=='9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df'
for f in ['def renameNatural {σ τ : Type*}', '| .constant a => .constant a','| .var i => .var (f i)','| .add p q => .add (renameNatural f p) (renameNatural f q)','| .mul p q => .mul (renameNatural f p) (renameNatural f q)','def expression : Expr (Fin 9) := ExecutableJones.expression seed 0','(NineFreshJones.jonesModel V left right).trans','(NineLightQuartic.exists_quartic_iff left right).trans (source_iff V).symm','IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','(Semiformula.lMap embedding sourceSentence)ᴺ','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:assert f in s,f

print(json.dumps({'status':'PASS','session':SESSION,'module':MOD,'guard_slots':GUARDS,'overlay_links':LINKS,'axiom_reports':REPORTS,'scope':SCOPE},indent=2))
