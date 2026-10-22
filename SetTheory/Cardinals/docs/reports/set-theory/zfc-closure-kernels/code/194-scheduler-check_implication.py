#!/usr/bin/env python3
"""Check the shared implication core against actual K215 numeric providers.

Use --scheduler-dir to also check the separately proposed scheduler clients.
The default compiles the unchanged production enumeration clients.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import time

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--out', type=Path, required=True)
p.add_argument('--scheduler-dir', type=Path)
p.add_argument('--coqc', default='coqc')
p.add_argument('--coqchk', default='coqchk')
a = p.parse_args()
here = Path(__file__).resolve().parent
repo, out = a.repo.resolve(), a.out.resolve()
if out.exists() and any(out.iterdir()):
    raise SystemExit('--out must be empty or absent')
out.mkdir(parents=True, exist_ok=True)
(out / 'logs').mkdir()
base = repo / 'Computability/BusyBeaver/Research/ZFC/k225-formal'
actual = base / 'rocq/rocq-extension/coq/215'
deps = base / 'verification/k215/simplification/proposals/checked-transport/rocq_seed_rank/source'
sha = lambda b: hashlib.sha256(b).hexdigest()
version = subprocess.check_output([a.coqc, '--version'], text=True)
compat = 'version 8.' in version
receipt = {
    'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
    'version': version, 'stdlib_namespace_compatibility': compat,
    'scheduler_clients': a.scheduler_dir is not None,
    'sources': [], 'checks': [], 'full_tm_endpoint_rebuilt': False,
}
order = [('K230S', 'KCode230', deps / 'K230S/KCode230.v'),
         ('K230L', 'Codes230', deps / 'K230L/Codes230.v')]
expected = ['bf7f032ca4408f50dcee14d2b49d113fb442a717b585f0cfdfe48bf14e4908be',
            '09ad45fa4d67885f293a0709e13a7e0ea0e16b5d2094bbc1bb98aea0e7bce06a']
for (_, _, source), digest in zip(order, expected):
    if sha(source.read_bytes()) != digest:
        raise SystemExit('Numeric production provider hash mismatch: ' + str(source))
for name in ('Codes222', 'Thm222'):
    order.append(('K215F', name, actual / (name + '.v')))
for name in ('DominatedImplication', 'DomRho8'):
    order.append(('K215F', name, here / (name + '.v')))
for name in ('ThmDom', 'EnumPerm', 'L1_SoundPerm'):
    order.append(('K215F', name, actual / (name + '.v')))
if a.scheduler_dir:
    order.append(('K215F', 'CandidateScheduler', a.scheduler_dir / 'CandidateScheduler.v'))
for name in ('L1_CompPerm', 'SeedPerm'):
    source = a.scheduler_dir or actual
    order.append(('K215F', name, source / (name + '.v')))
for ns, name, source in order:
    data = source.read_bytes()
    compiled = data.replace(b'From Stdlib ', b'From Coq ') if compat else data
    dest = out / ns / (name + '.v')
    dest.parent.mkdir(exist_ok=True)
    dest.write_bytes(compiled)
    receipt['sources'].append({
        'module': ns + '.' + name, 'source': str(source),
        'sha256': sha(data), 'compiled_sha256': sha(compiled),
        'namespace_alias_count': data.count(b'From Stdlib ') if compat else 0,
    })
flags = ['-Q', 'K230S', 'K230S', '-Q', 'K230L', 'K230L', '-Q', 'K215F', 'K215F']
def save():
    (out / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
def run(name, command):
    started = time.monotonic()
    result = subprocess.run(command, cwd=out, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / 'logs' / (name + '.log')).write_bytes(result.stdout)
    receipt['checks'].append({
        'name': name, 'command': command, 'exit_code': result.returncode,
        'seconds': time.monotonic() - started, 'log_sha256': sha(result.stdout),
    })
    save()
    print(name, result.returncode, flush=True)
    if result.returncode:
        print(result.stdout.decode(errors='replace'))
        raise SystemExit(result.returncode)
for ns, name, source in order:
    run(ns + '.' + name, [a.coqc, *flags, ns + '/' + name + '.v'])
client = '''From K230L Require Import Codes230.
From K215F Require Import DominatedImplication DomRho8 Thm222 ThmDom EnumPerm L1_CompPerm SeedPerm.
Check (@DomRho8.dtruth : forall T, DomRho8.DomImp T -> T 0).
Check (@DomRho8.dmp : forall T, DomRho8.DomImp T -> forall a b, T (wim a b) -> T a -> T b).
Check (@DomRho8.drho8 : forall T, DomRho8.DomImp T -> forall a b c u, u <= a -> T (Codes230.rho8 a b c u)).
Check (@DomRho8.rho8_all : forall T, DomRho8.DomImp T -> forall a b c u, T (Codes230.rho8 a b c u)).
Check (seedPerm_complete : thm222 1 -> halts_from seedPerm).
Check (seedPerm_sound : halts_from seedPerm -> thm222 1).
Check (seedPerm_iff_thm : halts_from seedPerm <-> thm222 1).
Print Assumptions DominatedImplication.rho8_all.
Print Assumptions DominatedImplication.composition.
Print Assumptions DominatedImplication.lift_right.
Print Assumptions DominatedImplication.basisK.
Print Assumptions DominatedImplication.basisPeirce.
Print Assumptions DominatedImplication.basisS.
Print Assumptions DomRho8.rho8_all.
Print Assumptions DomRho8.rho8_all_of_restricted.
Print Assumptions seedPerm_iff_thm.
'''
(out / 'Client.v').write_text(client)
run('Client', [a.coqc, *flags, 'Client.v'])
run('coqchk', [a.coqchk, *flags, 'K215F.DominatedImplication', 'K215F.DomRho8', 'K215F.SeedPerm', 'Client'])
receipt['status'] = 'PASS'
save()
