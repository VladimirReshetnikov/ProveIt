#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-first-cut-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-first-cut-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='363ca49f42af37fac085571d5c662bfae1aea1b9bd7c2c04b5a268ae5c68c1a6' and H(A/'outer-result.json')=='71ce9cb13b491220d312251df3e4ee23656a0d8d9f7a414b54dcb56cfb138a91';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(35551,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1061 and s['runner_sha256']==H(P/'run.py')=='9407db622e6b203a1337d1d50677bba8b42c1fa09be00335873539d857c64448';r=s['rows'][0];n='Sign25FirstCut';assert r['module']==n and r['source_sha256']=='640863c2a99e53145994df26088adc40a054e4bb8154611fbc4099da699db84c'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='e871a81de3d113a81b0df6c74fb744bf2bf4d678d7fd3a84d9579970eacbc320'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
for mod,h in [('SharingSign25Squares','5a019d411c6966d8420c0b57ac35c7acc8415892bb533983dfb2abe9128a7063'),('SharingSign26Squares','49bddc37c95ec053d290fc8314dc7cea089f4cce33baec24ee000fc44d573eb3')]:
 v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert log.count('warning:')==3 and log.count('Variable name `p` is not explicitly referenced')==3 and 'sorryAx' not in log and 'error:' not in log
for th in ('old_ell_row','old_N0_row','new_N0_row'):assert f"'DiophantineConsistency.Sign25FirstCut.{th}' depends on axioms: [propext]" in log
for th in ('old_ell_zero','N0_eval'):assert f"'DiophantineConsistency.Sign25FirstCut.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-first-cut-prelaunch-frontier-independent/check.py';assert H(pre)=='b297c925992092d919e191b598a9bc763e6218119a62c6ac0bc5bad8c75ec108';
for name,h in [('nine-sharing-sign25-seed-squares-terminal-frontier-independent','8207d760d00d9df69137a6148da3565b8748afdf9246880eae8125feaabce9f9'),('nine-sharing-sign26-seed-squares-terminal-frontier-independent','a60bbcc769f385fd2ac4ac843ad661fa13a9668567e7f15157d3de4fa207911d')]:
 up=D/'reviews'/name/'check.py';assert H(up)==h;subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':35551,'guards':150,'links':1061,'scope':'product ell row and N0 transfer only; no full bridge'},sort_keys=True,indent=2))
