#!/usr/bin/env python3
"""Test mixed-row state merges of the frozen permutation252 candidate.

Delete q, keep r, redirect every target q to r, and choose the retained
read-0/read-1 rows from different original states. The candidate must keep
all 55 proved register-support rows byte-identical and dispatch96 fixed.
Strict affine rejection is diagnostic, not a lower-bound proof. All runtime
survivors get a literal blank run. Frozen source tables are never modified.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile
import time
from types import SimpleNamespace

sys.dont_write_bytecode = True
from permutation252_fold_search import Tracking, load_module
ROOT = Path(__file__).resolve().parents[4]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=180)
    ap.add_argument('--affine-fuel', type=int, default=1000)
    ap.add_argument('--boot-limit', type=int, default=1000000)
    args = ap.parse_args()
    if not __debug__ or min(args.seconds,args.affine_fuel,args.boot_limit) <= 0:
        ap.error('Assertions and positive bounds required')
    base = ROOT/'Computability/BusyBeaver/Research/ZFC'
    scratch = Path(tempfile.mkdtemp(prefix='zfc-permutation252-mixed-'))
    audit = load_module('mixed_merge_audit', base/'candidate252_independent_audit.py')
    source = base/'candidate-permutation252/zfc_permutation252_old.tm'
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == audit.EXPECTED_SHA
    original = audit.read_table(raw)
    table = {(str(q),b):(v,d,str(t)) for (q,b),(v,d,t) in original.items()}
    states = sorted({q for q,b in table},key=int)
    protected = {(str(q),b) for q,b in audit.BOX_PAIRS}
    strict_source = ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    (scratch/'strict.py').write_bytes(strict_source.read_bytes())
    sys.modules['cost_search'] = SimpleNamespace()
    strict = load_module('mixed_merge_strict',scratch/'strict.py')
    prog_source = ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    body = prog_source.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
    assert len(nodes) == 6459
    cases = []
    def visit(q,p):
        for bit,e in enumerate(nodes[q]):
            path = p+str(bit);op,*arg = e.split()
            if op == 'CN': visit(int(arg[0]),path);continue
            r = int(arg[0]) if arg else None
            for zero in ((True,False) if op == 'CD' else (None,)):
                physical = audit.NEWPHYS[r] if op in ('CI','CD') else r
                guard = (physical,zero) if op == 'CD' else None
                nxt = audit.successor(path,op,r,zero)
                effect = ('inc',physical) if op == 'CI' else ('dec',physical) if op == 'CD' and not zero else None
                right = [('b',int(c)) for c in (nxt or '')]
                right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
                cases.append((path,op,guard,strict.canon([('b',1)],right)))
    visit(0,'');assert len(cases) == 8391
    def check(current,i):
        p,op,guard,target = cases[i]
        try:
            rules,literal = strict.run(current,p,guard,target,halt=op=='CH',fuel=args.affine_fuel)
            assert literal > 0
            return True,sum(rules.values()),None
        except AssertionError as exc:
            return False,0,'fuel' if str(exc)=='symbolic fuel exhausted' else 'unsupported_symbolic_rule'
        except KeyError: return False,0,'missing_transition'
    began = time.monotonic();usage = defaultdict(set);cost = []
    for i in range(len(cases)):
        tracked = Tracking(table);ok,n,_ = check(tracked,i);assert ok,('baseline',i)
        cost.append(n)
        for row in tracked.used: usage[row].add(i)
    spares = [0]*65;spares[8] = 1
    boot_target = audit.paint('',40,[0]*9,spares,2)
    q,h,ones,_,_ = audit.run_prefix(original,82552)
    assert (q,h,ones) == (96,2,boot_target)
    # Protected targets cannot be deleted: even a target rewrite changes a
    # supporting row. For pairs of eligible states, fix a label orientation;
    # reversing that orientation is isomorphic and does not add a machine.
    forbidden = {'96'} | {q for q,b in protected} | {table[row][2] for row in protected}
    eligible = set(states)-forbidden
    recipes = []
    skipped_same_rows = 0
    for dead in sorted(eligible,key=int):
        for keep in states:
            if dead == keep or keep == '96': continue
            if keep in eligible and int(dead)>int(keep): continue
            for bit in (0,1):
                if (keep,bit) in protected: continue
                if table[dead,bit] == table[keep,bit]:
                    skipped_same_rows += 1;continue
                recipes.append((dead,keep,bit))
    result = {'status':'running','scope':'Mixed-row 251-state diagnostics, not a consistency/minimality proof.',
      'attribution':'Mira-Cult original254; Jeff verification; Wade compiler; mira-emmy public253; ProveIt permutation252; source27 strict affine checker.',
      'table_sha256':audit.EXPECTED_SHA,'logical_to_physical':list(audit.NEWPHYS),
      'baseline8391':'PASS','baseline_exact82552wholeboot':'PASS','protected_rows':55,
      'recipe':'Delete dead; redirect all its incoming targets to keep; replace just keep[bit] with original dead[bit], including target redirection.',
      'planned_recipes':len(recipes),'eligible_deletions':len(eligible),
      'skipped_identical_row_recipes':skipped_same_rows,'completed_recipes':0,'case_checks':0,
      'affine_fuel':args.affine_fuel,'wall_seconds_limit':args.seconds,'boot_limit':args.boot_limit,
      'survivors':[],'first_failures':[],'scratch':str(scratch),
      'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),strict_source,prog_source,source)},
      'command':[sys.executable,*sys.argv]}
    reasons = Counter();args.output.parent.mkdir(parents=True,exist_ok=True)
    def save():
        result['elapsed_seconds'] = time.monotonic()-began
        result['failure_reasons'] = dict(reasons)
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('BASELINE8391+82552 PASS; recipes',len(recipes),flush=True);save()
    for dead,keep,bit in recipes:
        if time.monotonic()-began >= args.seconds: result['status']='time_bound_partial';break
        candidate = {(q,b):(v,d,keep if t==dead else t) for (q,b),(v,d,t) in table.items() if q!=dead}
        v,d,t = table[dead,bit];candidate[keep,bit] = (v,d,keep if t==dead else t)
        assert len(candidate)==502 and all(candidate[row]==table[row] for row in protected)
        affected = usage[dead,0] | usage[dead,1] | usage[keep,bit]
        failed = None;reason = None
        for i in sorted(affected,key=cost.__getitem__):
            ok,_,reason = check(candidate,i);result['case_checks'] += 1
            if not ok: failed=i;break
        if failed is None:
            for i in range(len(cases)):
                ok,_,reason = check(candidate,i);result['case_checks'] += 1
                if not ok: failed=i;break
        if failed is None:
            entry = {'dead':int(dead),'keep':int(keep),'row':bit}
            encoded = ('#! start 64\n'+''.join(f'{q} {b} {v} {d} {t}\n' for (q,b),(v,d,t) in sorted(candidate.items(),key=lambda x:(int(x[0][0]),x[0][1])))).encode()
            targetfile = scratch/f'merge-{dead}-{keep}-{bit}.tm';targetfile.write_bytes(encoded)
            entry['table'] = str(targetfile);entry['sha256']=hashlib.sha256(encoded).hexdigest()
            q,h,ones='64',0,set()
            for tick in range(args.boot_limit+1):
                if (q,h,ones)==('96',2,boot_target): entry['boot']={'outcome':'exact_target_frame','steps':tick};break
                if q=='254': entry['boot']={'outcome':'halt','steps':tick};break
                if tick==args.boot_limit: entry['boot']={'outcome':'fuel_limit','steps':tick};break
                v,d,q=candidate[q,int(h in ones)]
                if v: ones.add(h)
                else: ones.discard(h)
                h+=1 if d=='R' else -1
            result['survivors'].append(entry);print('SURVIVOR',entry,flush=True)
        else: reasons[reason]+=1
        result['first_failures'].append([int(dead),int(keep),bit,failed])
        result['completed_recipes']+=1
        if result['completed_recipes']%5000==0:save()
    else: result['status']='completed'
    save();print(json.dumps({k:result[k] for k in ('status','completed_recipes','case_checks','survivors','elapsed_seconds')}),flush=True)

if __name__=='__main__':main()
