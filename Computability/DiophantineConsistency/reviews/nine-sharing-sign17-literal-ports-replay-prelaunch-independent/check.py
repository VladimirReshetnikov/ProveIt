#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-literal-ports-replay-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='d218055c1bc282c7204d6a8cb6ea4dfc34889c2237b146e1cad690b8fd1ab9cd' and sha(p/'source-manifest.json')=='ff2d6ebaf72afb0b4ba6470995d50bcd65cc60bbdae084bca2c24b3069bbf09c'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17LiteralPorts';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();imports=['DiophantineConsistency.MFCurrentKernel2011','DiophantineConsistency.ArithmeticMaskData','DiophantineConsistency.MFPaper1982Digits'];assert e['module']=='DiophantineConsistency.'+n and e['imports']==imports and sha(q)==sha(repo/e['source'])==e['source_sha256']=='3de8c3649e358607b85a8317a052b5ac2c0e34c24608ae5f89d1a918a7821540' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==imports and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('theorem beta_eq','theorem mu_eq','theorem omega_eq','theorem K_eq','theorem all_ports','CurrentWindowCarry2011.ports 0 = beta','(CurrentWindowCarry2011.ports 1 : ℚ) = K','CurrentWindowCarry2011.ports 2 = mu','CurrentWindowCarry2011.ports 3 = omega'):assert z in s
for f in ('current14-mf-base-only-attempt02-theorem-independent','nine-sharing-sign17-lines-kernel-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
state=json.loads((root/'research/nine-sharing-sign17-lines-kernel-check/attempt01/state.json').read_text());base=Path('/tmp/nine-sharing-sign17-lines-kernel-20261110');pins={'MFCurrentKernel2011':'33d748748d1fbbc4ecbb3ce932536375d2bdcb45ada96602b5298e3dc89b948f','ArithmeticMaskData':'fce25c7165a78f7825542d699689135a3e65e539b01325b5dcfbe0d1fbcc639b','MFPaper1982Digits':'ad962dcb90cd33a206fb3ebe9780804e5170a5651659a1dcc7a96c4481bd83b5'}
for name,pin in pins.items():
 z=base/'lib/DiophantineConsistency'/(name+'.olean');assert z.is_symlink() and state['overlay_links'][str(z)]==str(z.resolve()) and sha(z)==pin
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'replay structured four port identities in numeral-K context, no PDF/file or complete ancestry theorem'},indent=2))
