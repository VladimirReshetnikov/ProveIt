#!/usr/bin/env python3
"""Independent recorded-source and direct-provider audit of MF byte decoder."""
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'current2011-mf-decoder-explicit-term';N=R/'current2011-mf-natural-sum-probe';C=R/'current2011-mf-port-cast-probe';F=R/'current2011-mf-decoder-composition';Q=R/'current2011-mf-recipe-diagnostic';B=R/'current2011-mf-byte-binding'
def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
pins={P/'CurrentMFDecoderExplicit.lean':'e827d52dd16c3220e3df5068c7c7df1c2f63eb76be3547165c791d1d6e724ae7',P/'check-lean.py':'c21f86c6be37db6148d72d256845b058cdc2b562545afe231232d47029dd99e4',P/'state.json':'f0e062f99b4c4abc2579758d78a9a4b8b0a6aed0192515c01e9dc2b6c06cbab6',P/'outer-terminal.json':'60f4b28be1ab0e67efa39e08780e317d66005564f417c88769c805e93173347c',
 N/'CurrentMFNaturalSum.lean':'4f5598c161dd3c3e5c98371191ca3cde6df45d373aafb2bcaeeaf718e83aec78',N/'check-lean.py':'6b13ac8ccaf936ab01da66a845dd60d3a4e26f92a1c4fb4c85c7d12e774bdaee',N/'state.json':'64f0c12a6201e065253b963c340ff1e942dd65f037fa8e072642c7341b036131',N/'outer-terminal.json':'b19a955266136c8f25395c4478ff8b9dc3d215c31dfb19a9071e77f0276570ad',
 C/'CurrentMFPortCast.lean':'3671e374f9ff61a3e4f8fb62e7276b969eb650cdbf9e65911a05432d188a0f77',C/'check-lean.py':'48194991ea4a326d5bd6b3fbafc0d83ea65fe3c2b7be592cdd4c835aad8a5b85',C/'state.json':'198582049bf32060687651ef485b56e939003877de4b34e1c582a93350aa4b7d',C/'outer-terminal.json':'98284247cf8e00b87e49809be1754dd2783cc53edb87dcbd7707f23db94c439b',
 Q/'CurrentMFRecipe.lean':'a89084ea6ef3e258687500d1514f268bc56c55d1acb2b82110d2f7945ab9fbef',B/'CurrentMFBytes.lean':'28cea9e660af49aab6f5c0dab1675619075a9644d9b130f87f6bc1900b1f709c',F/'state.json':'27aa277e0cdb4202598b13cedb9376d1ae1e63509ba3aa61a0e2669225a8a082',F/'outer-terminal.json':'cd39089fa5b88aa14be7c47642c1ad17e4018345a8e6c72c80cd2f4db4dc0743',F/'compile.txt':'3e3a49f08d032ede516e6540228b704dc10bd09bf3060dbd7d3aada77821d3cb'}
for p,h in pins.items():need(H(p)==h,'pin '+str(p))
def compact(s):return re.sub(r'\s+','',s)
recipe=(Q/'CurrentMFRecipe.lean').read_text();draft=(B/'CurrentMFBytes.lean').read_text();decoder=(P/'CurrentMFDecoderExplicit.lean').read_text();nat=(N/'CurrentMFNaturalSum.lean').read_text();cast=(C/'CurrentMFPortCast.lean').read_text()
getdigits=lambda s:compact(s.split('def maskDigits : List ℕ :=',1)[1].split('theorem rho_eq',1)[0])
need(getdigits(recipe)==getdigits(draft),'recipe digits mismatch to external checker')
need('defrho:ℕ:=2^47' in compact(recipe) and 'defrho:ℕ:=2^47' in compact(draft),'radix')
need('defshiftedValue:ℕ:=Nat.ofDigitsrhomaskDigits+(rho^2011-1)' in compact(draft) and 'defbigBytes:Listℕ:=(Nat.digits256shiftedValue).reverse' in compact(draft),'draft byte definition')
z=compact(decoder);need('defshiftedValue:ℕ:=Nat.ofDigitsrhomaskDigits+(rho^2011-1)' in z and 'defbigBytes:Listℕ:=(Nat.digits256shiftedValue).reverse' in z,'decoder byte definition')
need('theoremdecode_mf:((Nat.ofDigits256((Nat.digits256(Nat.ofDigitsrhomaskDigits+(rho^2011-1))).reverse.reverse):ℕ):ℤ)=CurrentWindowCarry2011.ports3:=' in z,'decoder theorem statement')
need('theoremnatural_sum:Nat.ofDigitsrhomaskDigits+(rho^2011-1)=CurrentMasks2011.highPort+CurrentMasks2011.beta:=' in compact(nat),'natural sum statement')
need('theoremport_natural_cast:((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):ℤ)=CurrentWindowCarry2011.ports3:=' in compact(cast),'port cast statement')
expected=[(N,'CurrentMFNaturalSum',46385,'216a395f5b8c4618f888af095f12a497f09c76489c92b8548b3556555189aba1',180,{'natural_sum':{'propext'}}),
 (C,'CurrentMFPortCast',63979,'e129e4fd5e9d67b85a06268b31fc7cf54883e19565b93bbff7c23f5505d21c43',180,{'cast_add_port_param':{'propext'},'port_natural_cast':{'propext','Classical.choice','Quot.sound'}}),
 (P,'CurrentMFDecoderExplicit',80805,'de6ae438ffe08244be49fa20982a1936607ea2f2a68036d5172f368fe4448db6',240,{'natural_decode':{'propext','Classical.choice','Quot.sound'},'decode_mf':{'propext','Classical.choice','Quot.sound'}})]
for path,name,session,objhash,nslots,reports in expected:
 state=json.loads((path/'state.json').read_text());outer=json.loads((path/'outer-terminal.json').read_text())
 need(state['status']=='PASS' and outer['session_id']==session and outer['exit_code']==0 and len(state['runs'])==2 and all(x['exit']==0 for x in state['runs']) and len(state['direct_guard'])==nslots,'state/exit '+name)
 need(H(path/'deps.txt')==state['runs'][0]['log_sha256'] and H(path/'compile.txt')==state['runs'][1]['log_sha256'],'logs '+name)
 need(H(path/(name+'.lean'))==state['source_sha256'] and H(path/'check-lean.py')==state['driver_sha256'],'source/driver '+name)
 need(state['preflight_before_sha256']==state['preflight_after_sha256']=='f159489a58b1804d327a35b98ae75e64d746efe4605de0ce8a25ef3d92ca70b2','preflights '+name)
 for key,rec in state['direct_guard'].items():
  p=Path(key)
  if rec is None:need(not os.path.lexists(p),'unexpected '+key)
  else:need(p.is_file() and str(p.resolve())==rec['realpath'] and H(p)==rec['sha256'],'guard '+key)
 obj=Path('/tmp')/('current2011-mf-'+{'CurrentMFNaturalSum':'natural-sum-probe','CurrentMFPortCast':'port-cast-probe','CurrentMFDecoderExplicit':'decoder-explicit-term'}[name]+'-20261105')/(name+'.olean')
 need(H(obj)==state['object_sha256']==objhash,'object '+name)
 log=(path/'compile.txt').read_text();need(not any(x in log for x in ('error:','warning:','sorryAx')),'successful log '+name)
 parsed=re.findall(r"'DiophantineConsistency\."+name+r"\.(\w+)' depends on axioms: \[([^]]*)\]",log,re.S)
 need({n:{x.strip() for x in a.split(',')} for n,a in parsed}==reports,'axioms '+name)
decoderstate=json.loads((P/'state.json').read_text());need(decoderstate['dependencies']['CurrentMFNaturalSum']['sha256']==expected[0][3] and decoderstate['dependencies']['CurrentMFPortCast']['sha256']==expected[1][3],'composed predecessor objects')
fo=json.loads((F/'outer-terminal.json').read_text());fs=json.loads((F/'state.json').read_text());need(fo['session_id']==52217 and fo['exit_code']==1 and fs['status']=='FAILED' and 'excessive memory' in (F/'compile.txt').read_text(),'previous composition failure')
audit=D/'reviews/current2011-mf-partial-binding-independent';run=subprocess.run([sys.executable,'-I','-S','-B',str(audit/'check.py')],capture_output=True);need(run.returncode==0 and run.stdout==(audit/'result.json').read_bytes(),'external bytes prior audit')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_MF_DECODER_AUDIT','successful_sessions':[46385,63979,80805],'guard_slots':[180,180,240],'prior_failed_session':52217,'external_payloads':2,'beta_shifts':1,'scope':'Lean symbolic list decoder to actual port plus separate external file comparison; no Lean gzip/file semantics, K binding or new transitive ancestry.'},indent=2,sort_keys=True))
