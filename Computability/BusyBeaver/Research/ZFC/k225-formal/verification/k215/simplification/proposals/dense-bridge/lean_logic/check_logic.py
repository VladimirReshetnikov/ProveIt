#!/usr/bin/env python3
"""Fresh focused checks of the archived six-goal Lean implication refactor.

The input checkout is read only.  No existing .olean is copied or reused.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

TARGETS = [
    'BusyBeaver.ZFC.DominatedImplication', 'BusyBeaver.ZFC.DomRho8',
    'BusyBeaver.ZFC.KCodeDom', 'BusyBeaver.ZFC.Lukasiewicz',
    'BusyBeaver.ZFC.KThmK', 'BusyBeaver.ZFC.Numeric254',
    'BusyBeaver.ZFC.TarskiFalsity',
]
COMMON_AUDIT = '''import BusyBeaver.ZFC.KCodeDom
import BusyBeaver.ZFC.KThmK
import BusyBeaver.ZFC.Numeric254
open SetTheory.BusyBeaver.ZFC
universe u
example {A : Type u} {L : DominatedImplication.Language A} {T : A → Prop}
    (h : DominatedImplication.Restricted L T) (a b c v : A) :
    T (DominatedImplication.rho8 L a b c v) := DominatedImplication.rho8_all h a b c v
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b : A) : T (i a (i b a)) := Lukasiewicz.k h a b
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b c : A) :
    T (i (i a (i b c)) (i (i a b) (i a c))) := Lukasiewicz.s h a b c
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b : A) : T (i (i (i a b) a) a) := Lukasiewicz.peirce h a b
example {A : Type u} {i : A → A → A} {T : A → Prop}
    (h : Lukasiewicz.Implicational i T) (a b c : A) :
    T (i (i a b) (i (i b c) (i a c))) := Lukasiewicz.composition h a b c
example (n : Nat) : KCodeDom.CDom n ↔ KCode222.C222 n := KCodeDom.cdom_iff_c222
#print axioms DominatedImplication.rho8_all
#print axioms DominatedImplication.composition
#print axioms DominatedImplication.lift_right
#print axioms Lukasiewicz.k
#print axioms Lukasiewicz.s
#print axioms Lukasiewicz.peirce
#print axioms Lukasiewicz.composition
#print axioms DomRho8.rho8_all
#print axioms KCodeDom.cdom_iff_c222
#print axioms Tarski.complete
#print axioms KThmK.classical
#print axioms Numeric254.classical
'''
EXTENDED_AUDIT = '''import BusyBeaver.ZFC.DominatedImplication
open SetTheory.BusyBeaver.ZFC
#print axioms DominatedImplication.k
#print axioms DominatedImplication.peirce
#print axioms DominatedImplication.s
'''

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--lean', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    repo, out, lean = a.repo.resolve(), a.out.resolve(), a.lean.resolve()
    if out.exists():
        raise SystemExit('Refusing an existing output directory; a fresh build is required.')
    revision = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
    if revision != '57541fe0cfe3af62b4cb58747d8d1d7c16b338d5':
        raise SystemExit('The verifier requires the pinned baseline commit.')
    if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=repo,text=True):
        raise SystemExit('Use a pristine baseline checkout, with no tracked modifications.')
    roots = {'BusyBeaver': repo/'Computability/BusyBeaver/Lean',
             'FirstOrder': repo/'Logic/FirstOrder/Lean',
             'ZF': repo/'SetTheory/ZF/Lean'}
    seen, order = set(), []
    def source(m):
        return roots[m.split('.')[0]]/(m.replace('.', '/')+'.lean')
    def visit(m):
        if m in seen or m.split('.')[0] not in roots:
            return
        seen.add(m)
        for line in source(m).read_text().splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    visit(dep)
        order.append(m)
    for m in TARGETS:
        visit(m)
    archived = repo/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase12/upstream-merge/inputs/Lean'
    delivered = Path(__file__).resolve().parent/'refactor'
    if delivered.is_dir():
        archived = delivered
    overrides = {m: archived/(m.replace('.', '/')+'.lean') for m in
                 ['BusyBeaver.ZFC.DominatedImplication', 'BusyBeaver.ZFC.Lukasiewicz']}
    results = {'baseline_commit': subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
               'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),
               'scope':'Fresh focused closure only; full KEndpoint215 not rebuilt.',
               'targets': TARGETS, 'module_order':order, 'variants':{}}
    out.mkdir(parents=True)
    for variant in ['baseline','candidate']:
        work = out/variant
        work.mkdir()
        logs = work/'logs'
        logs.mkdir()
        for m in order:
            src = overrides.get(m, source(m)) if variant == 'candidate' else source(m)
            dst = work/(m.replace('.', '/')+'.lean')
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src,dst)
        (work/'CommonAudit.lean').write_text(COMMON_AUDIT)
        jobs = order+['CommonAudit']
        if variant == 'candidate':
            (work/'ExtendedAudit.lean').write_text(EXTENDED_AUDIT)
            jobs.append('ExtendedAudit')
        env = dict(os.environ, LEAN_PATH=str(work))
        records = []
        for m in jobs:
            rel = m.replace('.', '/')
            cmd = [str(lean),'-o',rel+'.olean',rel+'.lean']
            start = time.monotonic()
            r = subprocess.run(cmd,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
            elapsed = time.monotonic()-start
            (logs/(m+'.log')).write_text(r.stdout)
            record = {'module':m,'source_sha256':digest(work/(rel+'.lean')),
                      'returncode':r.returncode,'seconds':round(elapsed,3)}
            records.append(record)
            print(variant, m, r.returncode, round(elapsed,3), flush=True)
            if r.returncode:
                print(r.stdout,flush=True)
                (out/'failed.json').write_text(json.dumps(records,indent=2))
                raise SystemExit(1)
        results['variants'][variant] = records
    suffix='namespace SetTheory.BusyBeaver.ZFC.Tarski\n'
    old=source('BusyBeaver.ZFC.Lukasiewicz').read_text()
    new=overrides['BusyBeaver.ZFC.Lukasiewicz'].read_text()
    results['tarski_tail_byte_identical'] = old[old.index(suffix):] == new[new.index(suffix):]
    results['common_audit_byte_identical'] = (out/'baseline/logs/CommonAudit.log').read_bytes() == (out/'candidate/logs/CommonAudit.log').read_bytes()
    if not results['tarski_tail_byte_identical'] or not results['common_audit_byte_identical']:
        raise SystemExit('The preserved semantic tail or common axiom audit changed.')
    extended = (out/'candidate/logs/ExtendedAudit.log').read_text()
    if extended.count('does not depend on any axioms') != 3 or 'sorryAx' in extended:
        raise SystemExit('The additional generic basis audit did not report three axiom-free theorems.')
    results['metrics']={}
    for variant in ['baseline','candidate']:
        paths=[out/variant/(m.replace('.','/')+'.lean') for m in overrides]
        results['metrics'][variant]={'proof_bytes':sum(x.stat().st_size for x in paths),'physical_lines':sum(len(x.read_bytes().splitlines()) for x in paths)}
    (out/'result.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({k:results[k] for k in ['tarski_tail_byte_identical','common_audit_byte_identical','metrics']},indent=2))

if __name__ == '__main__':
    main()
