#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-all-cuts-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-all-cuts-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'9df2673dfbe6180174f1768b1fafea8b2b8400e6f509ba2ab648947854b7f0f9','Sign33ForwardAllCuts-compile.txt':'5a17c2d0e25579e8db1bdf655fd33002bf912fb191c54de7d061b12ab411ef6b','outer-observation.json':'ac6798ada6674dbd17302554957b69687990edb4cc1e4b09e5f0e537182349a3'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(92937,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardAllCuts' and r['source_sha256']=='2fabc1accbddf85f43399b1bbd9bf1efeb4cece5c550ae24fed0f3bae56767f6' and r['object_sha256']=='c50b0dd8f83a448eeebbc441f36d903c316d764a8722590dfb51facfdae6b916'
assert h(p/'src/DiophantineConsistency/Sign33ForwardAllCuts.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardAllCuts.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardAllCuts-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardAllCuts-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('all_cuts_of_core',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardAllCuts\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33ForwardGap': 'e35f9ca9bc90675ed64d25c28c3abbc4b203ddb3a6e5a3af6abb6e82ab74f795', 'DiophantineConsistency.Sign33ForwardGroup00': '74257d5b86784d8674d052c40fead9afe6f90a45d372b0d6219f75442a59a9cc', 'DiophantineConsistency.Sign33ForwardGroup01': 'a4f6e2fc5d46f70f3cd6c4e3c0c4a154c7e1592117fcfdae799a2f1d72838542', 'DiophantineConsistency.Sign33ForwardGroup02': '17586f6302f4986996edb54f85eb8aad51990a57941aa09b2d2bd56b5d537540', 'DiophantineConsistency.Sign33ForwardGroup03Positive': '3c9c631307cb74d4ca716fbd5867ab67eb6978122f13434c7f51c33d30e4885e', 'DiophantineConsistency.Sign33ForwardInner': '313751eff9ff9cf5f760f1b40681eabd71f403377afa3229e84ed80530c86b88', 'DiophantineConsistency.Sign33ForwardLatePositive': '8d8150a645d643d763cf3fb3e29dfa2bf31f1eb163dcb6a1a96e05f7dd38554d', 'DiophantineConsistency.Sign33ForwardNormP': '7629f71fdaf8976674ca2650e9137e80f38367d0653a027cb53731e6ecdd2726', 'DiophantineConsistency.Sign33ForwardNormQRetry': '63cb5c455231c7536b955abe4485243d0bcfd111c89bd6862fae3de91470d24f', 'DiophantineConsistency.Sign33ForwardNormStrong': 'c6adcef3865edd72fca6880f2cc7974913f1595da0b1246cc736e00cf11fdbcc', 'DiophantineConsistency.Sign33ForwardNormU': '916bdc378cbef5d02a3382b27bf0f028deeb75690fe85bf0145b548e4dda6608', 'DiophantineConsistency.Sign33ForwardNormW': '6bf0ed0ce4b7b853fb5d741b16bb30fefc2556fa3552a3a80699e5d97cab7cfd', 'DiophantineConsistency.Sign33ForwardTau': '210d696667d13f50a12fcf2afe5d51391c0f72e88b9c77fc6337383f004fbeda', 'DiophantineConsistency.Sign33ForwardValueNegative': 'df7966db6beb033d7ad87887c142297f6412a2d923d3f7b8c5d104402539c5df'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==750 and len(s['overlay_links'])==1224
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':92937,'direct_guard_slots':750,'overlay_links':1224,'scope':'conditional same valuation 24-cut assembly; no Lean replay'},sort_keys=True,indent=2))
