#!/usr/bin/env python3
"""Point checks for audited E/F and checkpoint providers; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for folder,ch,rh in [('nine-seed38-jones-checkpoint43-kc-terminal-frontier-independent', '914d85674a649bf2ce136ea231d6a5b84d29d0dcfb71367875af7347bfd34277', '693ef9e9d45d7eadc6299e64388af91a344b49d47f8e75ecf01f878fa6ba24cd'), ('nine-seed38-jones-prefix-path18-41-terminal-frontier-independent', '470ff900fab224abe16c3c5e81cc51dc52f07dd62a8877c4fe2953b8b4392cba', '15fc98fc031182f5550ba6a135b2fe86d5b26f18896492192acab6da412f76e4'), ('nine-seed38-jones-prefix-group04-staged-terminal-frontier-independent', '31d6811cc6682276bb919729d3bc9f6465802abf6f2a134626cf7bcad193a26e', '153db18a7fbd10ce1ad77c25d25f7eaceeab5f9e2b877821392b4e1416129925'), ('nine-seed38-jones-dependent08-staged-terminal-frontier-independent', 'c9093ca2c52b810bf0f2d878bb513aa54502b0b2fa13146b11e4e35fbf62d26e', 'f59e7238d645a2eebab7b13fd342d5a1045ea3b53331e7e40620b2223407678c')]:
 q=D/'reviews'/folder
 if sha(q/'check.py')!=ch or sha(q/'result.json')!=rh:raise RuntimeError(('audit pin',folder))
 r=subprocess.run([sys.executable,'-I','-S','-B',str(q/'check.py')],capture_output=True,timeout=300)
 if r.returncode or r.stderr or r.stdout!=(q/'result.json').read_bytes():raise RuntimeError(('audit failure',folder,r.returncode,r.stderr.decode(errors='replace')))
draft=D/'research/nine-seed38-jones-terminal-cut-retry01-draft'
for n,h in [('Norm38MacroTerminalT', 'bda39c06525a17959e951b2c689ed5f31571324a3b0aacfbdf2f3b489d4bddd3'), ('Norm38MacroTerminalOutput', '921487eb186ddf29bed53603ed925c72d91a9284fcb3be75698eccbf10ffef59')]:
 if sha(draft/(n+'.lean'))!=h:raise RuntimeError(('source',n))
base=Path('/tmp/nine-seed38-jones-checkpoint43-kc-check-20261106/lib/DiophantineConsistency')
selected={}
for n,root,h in [('Norm38MacroKcValue', '/tmp/nine-seed38-jones-checkpoint43-kc-check-20261106/lib/DiophantineConsistency', '0b73715567a3ee4a5dd2a5117b35c489a3af154b9388e76a05d3e68e7b851d20'), ('Norm38MacroPath18to41', '/tmp/nine-seed38-jones-prefix-path18-41-check-20261106/lib/DiophantineConsistency', 'b245318d9c4049b569f3199955d2df27a31cdcfd49a1205ca2f8475801e32fa9'), ('Norm38MacroPrefixInputsB', '/tmp/nine-seed38-jones-prefix-group04-staged-check-20261106/lib/DiophantineConsistency', '43b71a21b7efa4d263709791c323ac49005a3e3b28542836890e094710474170'), ('Norm38MacroDependentOutput', '/tmp/nine-seed38-jones-dependent08-staged-check-20261106/lib/DiophantineConsistency', '39ae6b92258383e0505623a46c01a5ca71952561593a71090c0685508a7f8f58')]:
 p=Path(root)/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or not q.is_file() or q.resolve()!=p.resolve() or sha(p)!=h or sha(q)!=h:raise RuntimeError(('provider route',n))
 selected['DiophantineConsistency.'+n]={'realpath':str(p.resolve()),'sha256':h}
print(json.dumps({'status':'PASS_POINT_IN_TIME_PROVIDER_SURVEY','selected':selected,'scope':'Four audited Kc, path, input and terminal-node producers; no Lean, full semantics, JSON binding or dynamic trace.'},indent=2,sort_keys=True))
