#!/usr/bin/env python3
"""Fresh source-only build of balanced normalized K215 correspondence.

This deliberately does not claim a complete machine-to-ZFC endpoint rebuild.
Use --toolchain for an unpacked Debian Coq installation, or coqc on PATH.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time

ROOT = Path(__file__).resolve().parent

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--toolchain', type=Path)
    ap.add_argument('--recursive', action='store_true')
    args = ap.parse_args()
    out = args.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit('Use a fresh empty output directory.')
    work, logs = out/'work', out/'logs'
    work.mkdir(parents=True); logs.mkdir()
    env = os.environ.copy()
    if args.toolchain:
        tc = args.toolchain.resolve()
        env.update(OCAMLFIND_CONF=str(tc/'ocamlfind.conf'),
                   COQLIB=str(tc/'usr/lib/ocaml/coq'))
        coqc, coqchk = str(tc/'usr/bin/coqc'), str(tc/'usr/bin/coqchk')
    else:
        coqc, coqchk = shutil.which('coqc'), shutil.which('coqchk')
    if not coqc:
        raise SystemExit('coqc not found')
    version = subprocess.check_output([coqc, '--version'], env=env, text=True).strip()
    compat = 'version 8.18.' in version
    if not compat and 'version 9.1.' not in version:
        raise SystemExit('Supported recipe: Coq 8.18 or Rocq 9.1 (production lane not yet tested).')
    order = (['Compat818.v'] if compat else []) + [
        'deps/K230/RM.v', 'deps/K230/RMEquiv.v', 'deps/K230/Prog230.v',
        'deps/K230P/Bisim230.v', 'deps/K215F/Prog215.v', 'deps/K215F/DagPerm.v',
        'PathCodec.v', 'BisimMirror.v', 'BalancedBisim.v', 'NormalizedBisim.v',
        'NormalizedCert215.v', 'BalancedNormalized.v', 'NormalizedTree215.v',
        'Source215Composed.v', 'deps/K215F/Source215.v', 'EndpointClient.v']
    flags = ['-Q','deps/K230','K230','-Q','deps/K230P','K230P',
             '-Q','deps/K215F','K215F']
    receipt = {'schema':'balanced-normalized-k215-v1', 'toolchain':version,
        'coqc_sha256':sha(coqc), 'compatibility_import':compat,
        'scope':'Exact all-register SOURCE equivalence and public facade; not full binary/ZFC endpoint',
        'fresh':True, 'complete':False, 'sources':[], 'checks':[]}
    for rel in order:
        if rel == 'deps/K230/RMEquiv.v':
            src = ROOT/'deps/K230/RMEquiv.rocq91.v'
        elif rel == 'deps/K215F/Source215.v':
            src = ROOT/'Source215.v'
        else:
            src = ROOT/rel
        data = src.read_bytes()
        if rel == 'deps/K230/RMEquiv.v' and compat:
            needle = b'From K230 Require Import RM.'
            if data.count(needle) != 1:
                raise SystemExit('Unexpected compatibility import location')
            data = data.replace(needle, needle+b'\nRequire Import Compat818.')
        dst = work/rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_bytes(data)
        receipt['sources'].append({'module':rel, 'delivered_sha256':sha(src),
                                   'compiled_sha256':sha(dst)})
    def save():
        (out/'result.json').write_text(json.dumps(receipt, indent=2)+'\n')
    save()
    def run(name, cmd):
        print('CHECK', name, flush=True)
        log = logs/(name.replace('/','_')+'.log')
        start = time.monotonic()
        with log.open('w') as f:
            proc = subprocess.Popen(cmd, cwd=work, env=env,
                                    stdout=f, stderr=subprocess.STDOUT)
            _, status, usage = os.wait4(proc.pid, 0)
            proc.returncode = os.waitstatus_to_exitcode(status)
        content = log.read_text()
        row = {'name':name, 'argv':cmd, 'exit_code':proc.returncode,
               'seconds':round(time.monotonic()-start,3),
               'max_rss_kib':usage.ru_maxrss,
               'closed_reports':content.count('Closed under the global context'),
               'log_sha256':sha(log)}
        target = work/name
        if name.endswith('.v') and not proc.returncode:
            row['object_sha256'] = sha(target.with_suffix('.vo'))
        receipt['checks'].append(row); save()
        print(json.dumps(row), flush=True)
        if proc.returncode:
            print(content)
            raise SystemExit(proc.returncode)
        return content
    counts = {'BalancedNormalized.v':2, 'NormalizedTree215.v':3,
              'Source215Composed.v':2, 'deps/K215F/Source215.v':1,
              'EndpointClient.v':1}
    for rel in order:
        content = run(rel, [coqc, *flags, rel])
        if rel in counts and (content.count('Closed under the global context') != counts[rel]
                              or 'Axioms:' in content):
            raise SystemExit('Unexpected assumption report in '+rel)
    if args.recursive:
        if not coqchk:
            raise SystemExit('coqchk missing')
        run('recursive_concrete_client', [coqchk, *flags, '-silent', 'EndpointClient'])
    receipt['complete'] = True
    receipt['recursive_audit'] = 'passed' if args.recursive else 'not run'
    receipt['driver_sha256'] = sha(__file__)
    save()
    print('PASS_CLOSED_BALANCED_NORMALIZED_SOURCE', flush=True)

if __name__ == '__main__':
    main()
