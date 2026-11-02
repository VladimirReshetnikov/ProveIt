#!/usr/bin/env python3
"""Exact-degree check for the 2011-port specialization of the 69-row DAG."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
AUDIT=ROOT/'research/thirteen-variable-independent/audit.py'
GRAPH=ROOT/'research/thirteen-variable-independent/polynomial69.json'
PARENT=ROOT/'candidates/one-page-phase-split-carrier65-2471/polynomial.json'
INCOMING=ROOT/'con-zfc-diophantine-forms/192-pell-centers-fused-bounds/compact13/positive13_square.json'
MASK=ROOT/'Lean/DiophantineConsistency/CurrentMaskData2011.lean'
KERNEL=ROOT/'Lean/DiophantineConsistency/CurrentKernelData2011.lean'
PINS={AUDIT:'c05d7518d22ff5c639f20c8011f740d948b2567b4056849979c859c20ab86519',
 GRAPH:'3400069ead0bbf7b85d382c47fdd790bc18d68d9979e049f475d4e1c52d4182f',
 PARENT:'4814aa91ee692e68b82a55debbf29bda8f136cf51482fbf4ef84dc012670d421',
 INCOMING:'9574f3db6cfc549d565d278f84d7d9f0a53fec92cdcc05762c95d1e54db49c7c',
 MASK:'8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582',
 KERNEL:'529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c'}
def require(ok,why):
    if not ok:raise ValueError(why)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    for p,d in PINS.items():require(sha(p)==d,'pinned input drift: '+str(p))
    mask=MASK.read_text();kernel=KERNEL.read_text()
    require('def radix : ℕ := 2 ^ 47' in mask and 'def beta : ℕ := radix ^ 2011 - 1' in mask,'2011 beta definition')
    require('def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]' in mask,'mask tuple')
    require('def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in kernel,'fixed tuple')
    check=subprocess.run([sys.executable,'-I','-S',str(HERE/'check_rows.py')],capture_output=True,text=True,timeout=60)
    require(check.returncode==0 and not check.stderr,'exact DAG row check')
    row_result=json.loads(check.stdout);require(row_result['status']=='PASS','row result')
    spec=importlib.util.spec_from_file_location('pinned_thirteen_audit',AUDIT)
    require(spec is not None and spec.loader is not None,'audit loader')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    graph=json.loads(GRAPH.read_bytes());parent=json.loads(PARENT.read_bytes());incoming=json.loads(INCOMING.read_bytes())
    info=module.check_graph(graph,parent,incoming,False)
    require(info['exact_degree']==174 and info['live_gates']==69,'generic degree bound')
    require(info['leader_symbols']==module.VARIABLES+module.PORTS,'symbol order')
    wanted={'J':101,'gamma':1,'i':4,'eta':15,'w':14,'s':27,'f':8,'T':4}
    exp=[wanted.get(n,0) for n in module.VARIABLES]
    matches=[r for r in info['complete_leader'] if r[0][:13]==exp]
    expected_ports=[101,0,0,0]
    require(matches==[[exp+expected_ports,-128]],'selected full coefficient or other port terms')
    prime=1_000_000_007
    beta=(pow(2,47*2011,prime)-1)%prime
    coefficient=(-128*pow(beta,101,prime))%prime
    require(beta==878756698 and coefficient==937554773 and coefficient!=0,'2011 beta witness')
    # Substitution by constants cannot raise degree. The selected coefficient
    # survives 2011-port substitution, and xi -> xi+1 leaves the top form.
    print(json.dumps({'status':'PASS','gate_count':69,'degree':174,'prime':prime,
      'beta_mod_prime':beta,'selected_coefficient_mod_prime':coefficient,
      'witness_exponents':wanted,'generic_leader_sha256':info['leader_sha256'],
      'all_variable_leader_terms':info['complete_leader_terms'],
      'input_sha256':{str(p):d for p,d in PINS.items()},'row_check':row_result,
      'scope':'External exact sparse-leading-form check reusing the pinned prior audit. The 2011 beta specialization and positive shift are checked algebraically, not by Lean or PDF semantics; no model converse or iPRA proof is claimed.'},sort_keys=True))
if __name__=='__main__':main()
