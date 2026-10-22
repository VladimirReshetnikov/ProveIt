#!/usr/bin/env python3
"""Fresh focused Rocq/Coq check of the direct compiler, with kernel audit.

This is a calculus/enumerator component check, not a complete K215 endpoint build.
Coq 8.x compatibility changes only `From Stdlib` to `From Coq` in private copies.
"""
from pathlib import Path
import argparse, os, subprocess, json, hashlib, time, fcntl

ap = argparse.ArgumentParser()
ap.add_argument('--repo', type=Path, help='Optional ProveIt checkout; default uses bundled exact inputs')
ap.add_argument('--out', type=Path, required=True)
ap.add_argument('--coqc', type=Path, required=True)
ap.add_argument('--coqchk', type=Path, required=True)
ap.add_argument('--coq-root', type=Path, help='Optional extracted Debian/Ubuntu prefix, containing usr/lib/ocaml')
a = ap.parse_args()
here = Path(__file__).resolve().parent
base = Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
prod = base / 'rocq/rocq-extension/coq/215'
out = a.out.resolve()
out.mkdir(parents=True, exist_ok=False)
sources = out / 'sources'
logs = out / 'logs'; logs.mkdir()
env = dict(os.environ)
if a.coq_root:
    p = a.coq_root.resolve()
    env.update(COQLIB=str(p/'usr/lib/ocaml/coq'), OCAMLFIND_CONF=str(p/'etc/ocamlfind.conf'),
               OCAMLPATH=str(p/'usr/lib/ocaml'), CAML_LD_LIBRARY_PATH=str(p/'usr/lib/ocaml/stublibs'))
version = subprocess.check_output([str(a.coqc), '--version'], env=env, text=True)
compat8 = 'version 8.' in version
mods = ['K230S.KCode230', 'K230L.Codes230', 'K215F.Codes222', 'K215F.Thm222',
        'K215F.EnumPerm', 'K215F.DomRho8', 'K215F.L1_CompPerm', 'K215F.L1_SoundPerm',
        'K215F.SeedPerm', 'K215F.ThmDom', 'K215F.CompilerDomCompat']
receipt = {'status': 'RUNNING', 'scope': 'focused calculus, enumerator, unchanged seed interface, optional dominated compiler compatibility',
           'compiler_version': version.strip(), 'production_rocq_9_1_endpoint_rebuilt': False,
           'compatibility_namespace_rewrite': compat8, 'modules': []}
def sha(data): return hashlib.sha256(data).hexdigest()
for m in mods:
    ns, name = m.split('.')
    if not a.repo:
        src = here/'inputs'/ns/(name+'.v')
    elif name == 'CompilerDomCompat':
        src = here/'compat'/'CompilerDomCompat.v'
    elif ns == 'K215F':
        rel = prod/(name+'.v')
        src = here/'overlay'/rel
        if not src.exists(): src = a.repo/rel
    else:
        src = a.repo/base/'verification/k215/simplification/proposals/semantic-coverage/rocq/source'/ns/(name+'.v')
    b = src.read_bytes()
    text = b.decode()
    if compat8: text = text.replace('From Stdlib Require', 'From Coq Require')
    dest = sources/ns/(name+'.v'); dest.parent.mkdir(parents=True, exist_ok=True); dest.write_text(text)
    receipt['modules'].append({'module':m,'original_source':str(src),'original_sha256':sha(b),'compiled_sha256':sha(dest.read_bytes())})

client = '''From Coq Require Import List.
From K230L Require Import Codes230.
From K215F Require Import Thm222 EnumPerm L1_CompPerm L1_SoundPerm SeedPerm.

Example direct_type : forall X, thm222 X -> exists L, blk X L := compile_direct.
Example row_type : forall a b c u, exists L, blk (rho8 a b c u) L :=
  fun a b c u => compile_direct _ (W_r8 a b c u).
Example old_enum_type : thm222 1 -> enum_halts := enum_complete.
Example old_seed_complete_type : thm222 1 -> halts_from seedPerm := seedPerm_complete.
Example old_seed_sound_type : halts_from seedPerm -> thm222 1 := seedPerm_sound.
Example old_seed_iff_type : halts_from seedPerm <-> thm222 1 := seedPerm_iff_thm.
Print Assumptions direct_type.
Print Assumptions row_type.
Print Assumptions old_enum_type.
Print Assumptions old_seed_complete_type.
Print Assumptions old_seed_sound_type.
Print Assumptions old_seed_iff_type.
'''
(sources/'Client.v').write_text(client)
flags = []
for ns in ['K230S','K230L','K215F']: flags += ['-Q', str(sources/ns), ns]
flags += ['-Q', str(sources), '']
def save(): (out/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
save()
lock = open('/tmp/proveit-k215-proof-build.lock','w')
for item in receipt['modules'] + [{'module':'Client'}]:
    m = item['module']; f = sources/(m.replace('.','/')+'.v') if '.' in m else sources/(m+'.v')
    cmd = [str(a.coqc)] + flags + [str(f)]
    started = time.monotonic()
    with (logs/(m+'.log')).open('w') as log:
        fcntl.flock(lock,fcntl.LOCK_EX)
        try: p = subprocess.run(cmd,env=env,cwd=sources,stdout=log,stderr=subprocess.STDOUT)
        finally: fcntl.flock(lock,fcntl.LOCK_UN)
    item.update(exit_code=p.returncode,seconds=time.monotonic()-started)
    output = (logs/(m+'.log')).read_text()
    item.update(log_sha256=sha(output.encode()),object_sha256=sha(f.with_suffix('.vo').read_bytes()) if f.with_suffix('.vo').exists() else None)
    if m == 'Client': receipt['client'] = item; receipt['closed_client_reports']=output.count('Closed under the global context')
    save(); print(m, p.returncode, round(item['seconds'],3),flush=True)
    if p.returncode:
        receipt['status']='FAILED'; save(); print(output); raise SystemExit(p.returncode)
assert receipt['closed_client_reports'] == 6
cmd = [str(a.coqchk)] + flags + ['K215F.SeedPerm','K215F.CompilerDomCompat','Client']
started = time.monotonic()
with (logs/'coqchk.log').open('w') as log:
    fcntl.flock(lock,fcntl.LOCK_EX)
    try: p = subprocess.run(cmd,env=env,cwd=sources,stdout=log,stderr=subprocess.STDOUT)
    finally: fcntl.flock(lock,fcntl.LOCK_UN)
receipt['kernel']={'exit_code':p.returncode,'seconds':time.monotonic()-started,'command':cmd,'log_sha256':sha((logs/'coqchk.log').read_bytes())}
receipt['status']='PASS_FOCUSED_KERNEL' if p.returncode==0 else 'FAILED_KERNEL'
save(); print(receipt['status'],flush=True)
raise SystemExit(p.returncode)
