#!/usr/bin/env python3
"""Point checks for audited C substitution providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
audits=[('nine-seed38-jones-checkpoint28-41-j-terminal-frontier-independent', '9b3d130b31010f0014a7de606b93fb2e3ede9894d1c5b39481677b836909beb9', '6f82d237aee6711a54c0c48dcd3e94a8148ff8d614d0821b18215f792e4a1f7a'), ('nine-seed38-jones-live18-staged-terminal-frontier-independent', '63ecdb794bbb09df8baa50c7a19c5f1f2de15193c0d3e34ccbc7c1fdd7165765', 'd4424de55d8afca035515af5bf56899b02ae64e9e7e011fa256021f267d78eac'), ('nine-seed38-jones-prefix-group04-staged-terminal-frontier-independent', '31d6811cc6682276bb919729d3bc9f6465802abf6f2a134626cf7bcad193a26e', '153db18a7fbd10ce1ad77c25d25f7eaceeab5f9e2b877821392b4e1416129925'), ('nine-seed38-jones-prefix-group03-staged-terminal-frontier-independent', '7ff8505e755090bf5b29abe4b074bcd36546ed597cc43405b9e4ea6a87c72745', '2742892c8e514ac28db872993d219c639faf84961fd18f4852a03e01de81c8e3'), ('nine-seed38-jones-dependent03-staged-terminal-frontier-independent', '456db91d9870d3207907a5c115e33939ea1b423e46119ab658293beceafdb969', '0d0d2aaa5960eeaec7200494b62a585de92ce9da175dbb32d245ea8b9eff25e0'), ('nine-seed38-jones-checkpoint20-27-uy-terminal-frontier-independent', '2894cd041abc375f60d053f529fbbc295e6ec47d7906881e5fd73be9af54312f', '9af33b21c2f238b47631d19bf1ab9120df596c87b1250af1ddebf4eee4152a0a')]
for folder,ch,rh in audits:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
sources=[('Norm38MacroCInputs', 'c437c72394fcd4f78e5fc2d354e43e2b68bb4ea2088f88e8f9407d649003739c'), ('Norm38MacroCBW', '0e08969e782a06ad9aa4b1d7750e8a60d035a1c83564dc32efe2e5c338c4258c'), ('Norm38MacroCValue', '230c3642fbf7a9b36a1a45dd887ab4a20c734ad5e9cff4709c990e93276a85cb')]
draft=D/'research/nine-seed38-jones-checkpoint26-27-c-draft'
for n,h in sources:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint28-41-j-check-20261106/lib/DiophantineConsistency')
providers=[('Norm38MacroJPath', 'nine-seed38-jones-checkpoint28-41-j-check', 'd4a2147466024442645d58e1cd9a6f0943b8ecdcf30ab6b1a5a08eb620cf3ca6'), ('Norm38MacroLive18Group01', 'nine-seed38-jones-live18-staged-check', 'b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd'), ('Norm38MacroLive18Group03', 'nine-seed38-jones-live18-staged-check', '2589ac6c78d736a31bd3e851aaa0068d43ec0a10a10b3cb648b4df8b7da9d902'), ('Norm38MacroPrefixInputsB', 'nine-seed38-jones-prefix-group04-staged-check', '43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'), ('Norm38MacroPrefixGlarge', 'nine-seed38-jones-prefix-group03-staged-check', 'b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06'), ('Norm38MacroDependentW', 'nine-seed38-jones-dependent03-staged-check', '3f9a9d120dfc07e6dc0ce22145f5a9d76309838bbd7f6ae1f17f7b6efbb2b18d'), ('Norm38MacroLive18Group02', 'nine-seed38-jones-live18-staged-check', 'f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c'), ('Norm38MacroUYInputs', 'nine-seed38-jones-checkpoint20-27-uy-check', '26bf3e4788614e5d5efe6d131734539f551d9d8cbc50fb65b8b017d3b2ff828e'), ('Norm38MacroDependentC', 'nine-seed38-jones-dependent03-staged-check', '8a69d181c2584313ff4add42d2197020e387b888cd676fbfa4dc465a305bd281')]
selected={}
for n,root,h in providers:
 p=Path('/tmp')/(root+'-20261106')/'lib/DiophantineConsistency'/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Nine audited J/C and prefix providers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
