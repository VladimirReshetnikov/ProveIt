#!/usr/bin/env python3
"""Point-in-time alias-source and compiler-observation check; no Lean replay."""
from hashlib import sha256
from pathlib import Path
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')
DC=Path(__file__).resolve().parents[2]
base=DC/'research/ordinary12-ipra-bridge/compact44-symbolic-controller-alias-prototype'
files={
 'KernelAliasExplicit.lean':'57828e4f75c6c5361ad0ef4c05abf7376d516f857e3b1370826699f8806c9075',
 'observations03/KernelAliasExplicit.lean':'57828e4f75c6c5361ad0ef4c05abf7376d516f857e3b1370826699f8806c9075',
 'observations03/KernelAliasExplicit.log':'11b21e982b1c73c6726f21727b662baece49801e1df8cc8c7d4b120e8234d565',
 'observations03/terminal.json':'5212c10fe67203a9f8da72fb5ad687d15dc1b3251d7d3bc84aaf2463cc5e39ab',
 'observations04/AliasControllerUnit.log':'35518ff9511a8f95b4d0d3146a5a735ff436ee83f8d2d3cc85df762a5c2854ee',
 'observations04/terminal.json':'f15fde8adde32be6e51d2262df2507ea03638e2c654f6a988e626e91680f4f69',
}
objects={
 '/tmp/ipra-compact44-symbolic-unit-join/lib/KernelAliasExplicit.olean':'6f5201c9f051af543096f9447f4525ab2603c79c63261edc352c9709573424f4',
 '/tmp/ipra-compact44-symbolic-unit-join/lib/SymbolicKernelResidue.olean':'e3d3a2d356e45a9b742ccaf609792b2a7bcfdedf475ed4de0b31ee4e22e67302',
}
def need(ok,msg):
    if not ok: raise ValueError(msg)
def sha(path): return sha256(Path(path).read_bytes()).hexdigest()
def check():
    for path,pin in files.items(): need(sha(base/path)==pin,'source/receipt: '+path)
    for path,pin in objects.items(): need(sha(path)==pin,'object: '+path)
check()
good=json.loads((base/'observations03/terminal.json').read_text())['stages']
bad=json.loads((base/'observations04/terminal.json').read_text())['stages']
need(len(good)==1 and good[0]['module']=='KernelAliasExplicit' and good[0]['exit_code']==0 and
     good[0]['source_sha256']==files['KernelAliasExplicit.lean'] and
     good[0]['object_sha256']==objects['/tmp/ipra-compact44-symbolic-unit-join/lib/KernelAliasExplicit.olean'] and
     not good[0]['warning_present'] and not good[0]['sorry_present'],'successful observation')
need(len(bad)==1 and bad[0]['module']=='AliasControllerUnit' and bad[0]['exit_code']==1 and
     bad[0]['object_sha256'] is None,'failed unit observation')
badlog=(base/'observations04/AliasControllerUnit.log').read_text()
need('error: (kernel) excessive memory consumption detected' in badlog and
     'alias_gamma_unit' in badlog,'failed-unit output')
goodlog=(base/'observations03/KernelAliasExplicit.log').read_text()
for name in ('kernelAlias_eq','kernelAlias_mod'):
    need("'CompactSymbolicKernelAliasExplicit."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in goodlog,
         'missing axiom report: '+name)
need('sorryAx' not in goodlog and 'warning:' not in goodlog,'successful log')
check()
print(json.dumps({'status':'PASS_ALIAS_SOURCE_REVIEW','successful_alias_exit':0,
                  'unit_client_exit':1,'scope':'point-in-time source/artifact check, not Lean replay'},sort_keys=True))
