#!/usr/bin/env python3
"""Search an additional arbitrary row edit after a selected state deletion.

Candidate filtering uses the pinned strict affine instruction checker and
only its four existing register-box contracts. No sampled run is promoted
to a proof. The six source-impossible guards may be omitted as an explicitly
conditional phase assumption. Full retained-case checking is mandatory.
"""
import argparse
from collections import defaultdict, Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import time
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1] / 'source'
BASE = ROOT / 'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0, str(BASE))
import candidate252_independent_audit as audit


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class Tracking(dict):
    def __init__(self, rows):
        super().__init__(rows)
        self.used = set()
    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


def prepare(omit):
    frozen = BASE / 'candidate-permutation252/zfc_permutation252_old.tm'
    raw = frozen.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == audit.EXPECTED_SHA
    numeric = audit.read_table(raw)
    table = {(str(q), b): (w, d, str(t)) for (q,b),(w,d,t) in numeric.items()}
    sys.modules['cost_search'] = SimpleNamespace()
    strict_path = ROOT / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    strict = load('repair_strict_affine', strict_path)
    prog = ROOT / 'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    text = prog.read_text().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\(('+edge+r'),\s*('+edge+r')\)', text)
    assert len(nodes) == 6459
    cases = []
    def visit(q, prefix):
        for b,e in enumerate(nodes[q]):
            pc = prefix + str(b)
            op,*args = e.split()
            if op == 'CN':
                visit(int(args[0]),pc)
                continue
            r = int(args[0]) if args else None
            for zero in ((True,False) if op == 'CD' else (None,)):
                phys = audit.NEWPHYS[r] if op in ('CI','CD') else r
                branch = (phys,zero) if op == 'CD' else None
                nxt = audit.successor(pc,op,r,zero)
                effect = ('inc',phys) if op == 'CI' else ('dec',phys) if op == 'CD' and not zero else None
                right = [('b',int(c)) for c in nxt] if nxt is not None else []
                right += [('r',0,1,(41 if nxt is None else 40)-len(nxt or '')),('b',1),('box',('plain',effect))]
                cases.append((pc,branch,strict.canon([('b',1)],right),op == 'CH'))
    visit(0,'')
    assert len(cases) == 8391
    retained = [i for i in range(len(cases)) if i not in omit]
    def check(current, i):
        pc,branch,target,halt = cases[i]
        try:
            rules,literal = strict.run(current,pc,branch,target,halt=halt,fuel=1000)
            assert literal > 0
            return True,sum(rules.values()),None
        except AssertionError as ex:
            return False,0,str(ex)
        except KeyError as ex:
            return False,0,'missing '+str(ex)
    usage = defaultdict(set)
    costs = {}
    for i in retained:
        traced = Tracking(table)
        ok,cost,reason = check(traced,i)
        assert ok,(i,reason)
        costs[i] = cost
        for row in traced.used:
            usage[row].add(i)
    q,h,ones,_,_ = audit.run_prefix(numeric,82552)
    spares = [0]*65
    spares[8] = 1
    assert (q,h,ones) == (96,2,audit.paint('',40,[0]*9,spares,2))
    print('BASELINE retained',len(retained),'whole boot82552 PASS',flush=True)
    return table,check,retained,usage,costs


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--seconds',type=float,default=900)
    ap.add_argument('--folds',default='204:252,113:23,34:68')
    ap.add_argument('--exclude-phase-guards',action='store_true')
    args = ap.parse_args()
    omit = {8202,8203,8204,8358,8359,8360} if args.exclude_phase_guards else set()
    began = time.monotonic()
    table,check,retained,usage,costs = prepare(omit)
    states = sorted({q for q,b in table},key=int)
    protected = {(str(q),b) for q,b in audit.BOX_PAIRS} | {('96',b) for b in (0,1)}
    result = {'scope':'Additional single-row full-action repairs after selected uniform state deletions; finite affine diagnostics conditional on unchanged box contracts and optional original phase invariant.',
              'table_sha256':audit.EXPECTED_SHA,'excluded_phase_cases':sorted(omit),
              'fuel':1000,'tested':0,'checks':0,'survivors':[],'families':[],
              'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    out = args.output
    out.parent.mkdir(parents=True,exist_ok=True)
    journal = out.with_suffix('.jsonl')
    def save():
        result['elapsed_seconds'] = time.monotonic()-began
        out.write_text(json.dumps(result,indent=2)+'\n')
    with journal.open('w') as record:
        for fold in args.folds.split(','):
            dead,target = fold.split(':')
            current = {k:(w,d,target if t==dead else t) for k,(w,d,t) in table.items() if k[0]!=dead}
            assert all(current[k] == table[k] for k in protected)
            # Choose a diagnostic failure as a complete hitting set for any
            # one-row repair: a row not observed by that deterministic failed
            # trace cannot affect this failure.
            fold_usage = set.union(*(usage[k] for k in table if k[0]==dead or table[k][2]==dead))
            failed_case = None
            failure_trace = None
            for i in sorted(fold_usage,key=lambda i:(costs[i],i)):
                traced = Tracking(current)
                ok,_,reason = check(traced,i)
                if not ok:
                    failed_case,failure_trace = i,traced.used
                    break
            assert failed_case is not None
            edits = sorted(failure_trace-protected,key=lambda k:(int(k[0]),k[1]))
            family = {'deleted':int(dead),'target':int(target),'first_failure_case':failed_case,
                      'repair_rows':[list(k) for k in edits],'tested':0,'survivors':[]}
            result['families'].append(family)
            print('FOLD',dead,target,'failed',failed_case,'repair rows',len(edits),flush=True)
            for row in edits:
                if row not in current:
                    continue
                affected = sorted(fold_usage | usage[row],key=lambda i:(costs[i],i))
                order = [failed_case]+[i for i in affected if i!=failed_case]
                for w in (0,1):
                    for d in ('L','R'):
                        for dst in states+['254']:
                            if dst==dead or (w,d,dst)==current[row]:
                                continue
                            if time.monotonic()-began>args.seconds:
                                result['status']='time_bound_partial'
                                save()
                                return
                            changed = current.copy()
                            changed[row]=(w,d,dst)
                            failure = None
                            for i in order:
                                ok,_,reason = check(changed,i)
                                result['checks']+=1
                                if not ok:
                                    failure=i
                                    break
                            if failure is None:
                                for i in retained:
                                    ok,_,reason = check(changed,i)
                                    result['checks']+=1
                                    if not ok:
                                        failure=i
                                        break
                            entry = {'deleted':int(dead),'target':int(target),'row':[int(row[0]),row[1]],
                                     'action':[w,d,int(dst)],'failure':failure}
                            result['tested']+=1
                            family['tested']+=1
                            if failure is None:
                                family['survivors'].append(entry)
                                result['survivors'].append(entry)
                                path=out.parent/f'repair_{dead}_{target}_{row[0]}_{row[1]}_{w}{d}{dst}.tm'
                                path.write_text('#! start 64\n'+''.join(f'{q} {b} {x} {e} {t}\n' for (q,b),(x,e,t) in sorted(changed.items(),key=lambda p:(int(p[0][0]),p[0][1]))))
                                entry['path']=str(path)
                                print('SURVIVOR',entry,flush=True)
                            record.write(json.dumps(entry,separators=(',',':'))+'\n')
                            if result['tested']%1000==0:
                                save()
            save()
    result['status']='completed'
    result['journal_sha256']=hashlib.sha256(journal.read_bytes()).hexdigest()
    save()
    print(json.dumps({k:result[k] for k in ('status','tested','checks','survivors','elapsed_seconds')}),flush=True)


if __name__ == '__main__':
    main()
