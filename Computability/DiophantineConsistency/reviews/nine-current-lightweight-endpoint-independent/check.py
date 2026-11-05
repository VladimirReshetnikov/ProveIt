#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';BAD=R/'nine-current-lightweight-endpoint-draft';GOOD=R/'nine-current-lightweight-endpoint-retry';Q=R/'nine-current-lightweight-jones-probe/attempt01/state.json'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert sha(Q)=='5003d43d0deb8c7339766d9ea62bb3866a66fba9d4d277fcca5f4afcf0db33d4'
checks=[]
for P,attempt,session,exit,status,sr,pin in [(BAD,'attempt01',55005,1,'FAILED','73c706d3872c2627d8a4f033d272f834680cb923e320a9b1aeba30898ff559d4',None),(GOOD,'attempt02',3591,0,'PASS','926118c86d316f2b47c5720f64283d84dcb3f3e6abb0c6eb9bb0409c69ca2c0e','a42b32c8876524e12fbad37bb404239c24d9d86b0c0378a3d41983fccb9b5072')]:
 A=P/attempt;d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert (d['status'],o['actual_session'],o['exit_code'],d['base_state_sha256'])==(status,session,exit,sha(Q))
 assert len(d['rows'])==1;r=d['rows'][0];assert r['module']=='IPRANineCurrent' and r['source_sha256']==sr==sha(A/'source.lean')==sha(P/'IPRANineCurrent.lean')
 for typ,expected in [('deps',0),('compile',exit)]:
  run=r[typ];log=A/('IPRANineCurrent-'+typ+'.txt');assert run['exit']==expected and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids'] and sha(log)==run['log_sha256']
  assert run['rss_limit_bytes']==4*1024**3 and run['host_floor_bytes']==10*1024**3 and run['timeout_seconds']==120 and run['sampling_interval_seconds']==0.1 and run['peak_session_rss_bytes']<4*1024**3 and run['min_host_available_bytes']>=10*1024**3
 assert len(r['direct_guard'])==250 and len(d['overlay_links'])==1054
 for key,v in r['direct_guard'].items():
  p=pathlib.Path(key)
  if v is None:assert not os.path.lexists(p),p
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
 for key,v in d['overlay_links'].items():assert pathlib.Path(key).is_symlink() and str(pathlib.Path(key).resolve())==v,key
 assert r['dependencies']['DiophantineConsistency.ModelJonesNine']['sha256']=='9db3f4363700e3d3ec2a7d411884be7c717192218a8d50ab43cc798e2ba1b425'
 log=(A/'IPRANineCurrent-compile.txt').read_text()
 if status=='FAILED':assert 'Invalid field `rename`' in log and 'rewrite' in log and 'sorryAx' in log and not r.get('object_sha256')
 else:
  assert sha('/tmp/nine-light-endpoint-retry-20261105/lib/DiophantineConsistency/IPRANineCurrent.olean')==r['object_sha256']==pin
  reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log);names=['DiophantineConsistency.ModelJonesNine.jonesModel']+['DiophantineConsistency.IPRANineCurrent.'+n for n in ['polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence']];assert [n for n,_ in reports]==names
  assert all([x.strip() for x in ax.split(',')]==['propext','Classical.choice','Quot.sound'] for _,ax in reports)
 checks.append({'session':session,'status':status,'outer_exit':exit,'child_exits':[r['deps']['exit'],r['compile']['exit']],'guard_slots':len(r['direct_guard']),'overlay_links':len(d['overlay_links']),'state_sha256':sha(A/'state.json')})
assert sha(GOOD/'attempt02/state.json')=='00149b46384d4263ba6ddee3af1d09576735342b0bd58ac4a019438d8f1fffe6' and sha(GOOD/'run.py')=='fa3053b8fd11f134debaf0943c3e3d5fbc1120ebf460f3e34098c3a696e604d9'
a=(BAD/'IPRANineCurrent.lean').read_text();b=(GOOD/'IPRANineCurrent.lean').read_text();ren='''namespace DiophantineConsistency.NatExpr\n\n/-- The same recursive natural-syntax renaming as the heavier compaction module. -/\ndef rename {σ τ : Type*} (f : σ → τ) : NatExpr σ → NatExpr τ\n  | .constant a => .constant a\n  | .var i => .var (f i)\n  | .add p q => .add (p.rename f) (q.rename f)\n  | .mul p q => .mul (p.rename f) (q.rename f)\n\nend DiophantineConsistency.NatExpr\n\n''';a=a.replace('namespace DiophantineConsistency.IPRANineCurrent',ren+'namespace DiophantineConsistency.IPRANineCurrent',1).replace('  have hB := HACurrentEquation2011.polynomialBridge V','  have currentBridge : HAExpressionAssembly.PolynomialBridge ObjectCurrentEquation2011.naturalExpression :=\n    fun W _ _ => HACurrentEquation2011.polynomialBridge W\n  have hB := currentBridge V');assert a==b
old=(D/'Lean/DiophantineConsistency/WitnessCompaction.lean').read_text();body=b.split('def rename {σ τ : Type*}',1)[1].split('\n\nend DiophantineConsistency.NatExpr',1)[0];oldbody=old.split('def rename {τ : Type*}',1)[1].split('\n\n@[simp]',1)[0];assert body==oldbody
for f in ['ObjectCurrentEquation2011.naturalExpression.splitNatural.1.rename Sum.inr','ObjectCurrentEquation2011.naturalExpression.splitNatural.2.rename Sum.inr','def expression : Expr (Fin 9) := ExecutableJones.expression seed 0','(ModelJonesNine.jonesModel V left right).trans','(NineLightQuartic.exists_quartic_iff left right).trans (source_iff V).symm','IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding','(Semiformula.lMap embedding sourceSentence)ᴺ','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:assert f in b,f
print(json.dumps({'status':'PASS','checks':checks,'scope':'Nine-natural-variable abstract syntax and standard/native/GG endpoints; no literal graph, numerical degree or file theorem; no Lean replay.'},indent=2))
