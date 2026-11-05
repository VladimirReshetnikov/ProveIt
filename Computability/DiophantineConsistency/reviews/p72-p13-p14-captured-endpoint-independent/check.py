#!/usr/bin/env python3
import pathlib,json,hashlib,os,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/p72-p13-p14-captured-endpoint-replay';A=P/'attempt01';B=D/'Lean/DiophantineConsistency/Compact44';OUT=pathlib.Path('/tmp/p72-p13-p14-captured-endpoint-20261105');TOOL=D/'research/ordinary13-p72-endpoint/tools'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')=='69b125385c7eff4a1ae2efcde94f777e16c591fb281b07e0132500173f9df2aa'
assert (d['status'],o['actual_session'],o['exit_code'])==('PASS',51877,0)
assert sha(P/'run.py')==d['runner_sha256']=='0459eb2c455a9ce452468bf0189d406fb9523eae556a4dc2eacacc219c4fd235'
for path,h in d['pins'].items():assert sha(path)==h,path
names=['IPRAOrdinary72','IPRAOrdinary72P14'];pins=['2a296211af161f8c8b7f4173f81c12e64dffeede4a76adf455928d7b9b54558e','b88eb198df9ae1a2f7366f10c5b5363aee95dc0d3546146a45d7cb39b9aada03'];objs=['d667e5803d918e9211c170e55a03d56d8b62b42f43b152d8ab526905ae26a3b3','3c47dcbbd39cbb2f89092e40d747366589cc618da7bdf9765016554d65e82468'];assert [r['module'] for r in d['records']]==['DiophantineConsistency.Compact44.'+n for n in names]
for n,pin,objhash,r in zip(names,pins,objs,d['records']):
 s=(B/(n+'.lean')).read_text();assert sha(B/(n+'.lean'))==r['source_sha256']==pin==sha(OUT/'src/DiophantineConsistency/Compact44'/(n+'.lean'))
 for f in ['theorem positiveBridge : PositiveModelBridge expression','theorem native_equivalence : nativeTheory ⊢','theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢','IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘','∼mappedNativeRefutation embedding','CompactSymbolicPortProjections.portsInt (paramKernel rho)']:assert f in s,(n,f)
 for run,typ in zip(r['runs'],['deps','compile']):
  assert run['exit']==0 and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids'] and sha(A/(n+'-'+typ+'.txt'))==run['log_sha256']
  assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['timeout_seconds']==180 and run['sampling_interval_seconds']==0.1 and '-M4000' in run['command']
  assert run['peak_session_rss_bytes']<5*1024**3 and run['min_host_available_bytes']>=10*1024**3
 obj=OUT/'lib/DiophantineConsistency/Compact44'/(n+'.olean');assert sha(obj)==r['object_sha256']==objhash
 for key,v in r['direct_guard'].items():
  p=pathlib.Path(key)
  if v is None:assert not os.path.lexists(p),p
  else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
 reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",(A/(n+'-compile.txt')).read_text());expected=['positiveBridge','native_equivalence','standard_equivalence','reference_equivalence'];expected=(['P72P14.zero_iff']+expected if n.endswith('P14') else expected)
 assert len(reports)==len(expected)
 for (name,axioms),e in zip(reports,expected):assert (name==e or name.endswith('.'+e)) and [x.strip() for x in axioms.split(',')]==['propext','Classical.choice','Quot.sound']
assert d['records'][1]['direct_inputs']['DiophantineConsistency.Compact44.IPRAOrdinary72']['sha256']==objs[0]
assert len(d['overlay_links'])==d['provider_inventory_entries']==2217
for rel,(kind,target) in d['overlay_links'].items():
 p=OUT/'lib'/rel;assert p.is_symlink() and str(p.resolve())==target and kind in ('dir','file'),p
for script,file,output in [('generate_p72.py',B/'P72Graph.lean','p13-binding.txt'),('generate_p14.py',B/'IPRAOrdinary72P14.lean','p14-binding.txt')]:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(TOOL/script),'--check',str(file)],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/output).read_bytes(),script
assert '⟨Z, A0, A1, Aa, As, g97⟩' in (B/'P72Graph.lean').read_text() and '⟨A0, A1, Aa, As, AE, P14⟩' in (B/'IPRAOrdinary72P14.lean').read_text()
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check-graph-producer.py')],capture_output=True);assert q.returncode==0 and not q.stderr and q.stdout==(P/'graph-producer-result.json').read_bytes()
rp=D/'research/p65-reverse-provider';manifest=json.loads((rp/'manifest.json').read_text());receipt=json.loads((rp/'results.json').read_text());name='DiophantineConsistency.Compact44.P72Graph';row=next(x for x in manifest['order'] if x['module']==name);rec=receipt[name]
canonical=(B/'P72Graph.lean').read_text();assert pathlib.Path(row['shim']).read_text()==canonical.replace('import DiophantineConsistency.Compact44.FreeJSumSquares\n','import FreeJSumSquares\n',1)
assert sha(row['shim'])==row['shim_sha256']==rec['shim_sha256'] and sha(rec['object'])==rec['object_sha256']==d['pins']['/tmp/p64-independent-captured-replay/lib/DiophantineConsistency/Compact44/P72Graph.olean'] and sha(rec['log'])==rec['log_sha256'] and 'exit: 0, elapsed:' in pathlib.Path(rec['log']).read_text()
print(json.dumps({'status':'PASS','outer_session':51877,'child_exits':[r['exit'] for x in d['records'] for r in x['runs']],'guard_slots':[len(r['direct_guard']) for r in d['records']],'overlay_links':len(d['overlay_links']),'producer_object_sha256':rec['object_sha256'],'scope':'Captured P64/P65 ancestry; standard/native/equality-only endpoints; JSON graph blocks externally matched, six derived constants are fixed leaves. No fresh base rebuild, Lean JSON/gzip theorem or new degree proof.'},indent=2))
