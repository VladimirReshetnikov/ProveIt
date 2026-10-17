#!/usr/bin/env python3
"""Derived from pinned ProveIt lazy context search: full write/move/target actions.

Lazy two-incoming-target deletions in the frozen permutation252 table.

An unassigned incoming row interrupts a diagnostic trace before its target
is read. Each branch restarts the exact strict executor from that case's
initial symbolic state. A failure before another unassigned read rejects
all completions of that partial assignment. Joint compensation is allowed.
All8391 cases and literal blank boot are mandatory for concrete survivors.
A finite time bound leaves an explicit disjoint assignment frontier.
The55 Box rows, both dispatch96 rows and start64 are unchanged. No Lean/Coq
build, network access, frozen-machine edit or minimality claim occurs.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import platform
import re
import sys
import tempfile
import time
from types import SimpleNamespace
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'source/Computability/BusyBeaver/Research/ZFC'))
from permutation252_context_search import Tracking, load
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1] / 'source'

class NeedTarget(Exception):
    def __init__(self, index): self.index = index

class PartialTable(dict):
    def __init__(self, rows, pending):
        super().__init__(rows)
        self.pending = pending
    def __getitem__(self, key):
        if key in self.pending:
            raise NeedTarget(self.pending[key])
        return super().__getitem__(key)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--scratch', type=Path)
    parser.add_argument('--seconds', type=float, default=900)
    parser.add_argument('--exclude-phase-guards', action='store_true')
    parser.add_argument('--deletions', type=str)
    parser.add_argument('--affine-fuel', type=int, default=1000)
    parser.add_argument('--boot-limit', type=int, default=1000000)
    args = parser.parse_args()
    if not __debug__: parser.error('Assertions must remain enabled')
    if min(args.seconds,args.affine_fuel,args.boot_limit) <= 0: parser.error('Positive bounds required')
    repo = args.repo.resolve()
    base = repo / 'Computability/BusyBeaver/Research/ZFC'
    work = args.scratch.resolve() if args.scratch else Path(tempfile.mkdtemp(prefix='zfc-perm252-lazy-context-'))
    if work == repo or repo in work.parents:
        parser.error('External scratch required')
    work.mkdir(parents=True, exist_ok=True)
    audit = load('permutation252_lazy_context_audit', base / 'candidate252_independent_audit.py')
    frozen = base / 'candidate-permutation252/zfc_permutation252_old.tm'
    raw = frozen.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == audit.EXPECTED_SHA
    numeric = audit.read_table(raw)
    table = {(str(q), b): (v, d, str(t)) for (q, b), (v, d, t) in numeric.items()}
    states = sorted({q for q, b in table}, key=int)
    protected = {(str(q), b) for q, b in audit.BOX_PAIRS}
    assert len(states) == 252 and len(table) == 504 and len(protected) == 55
    strict_source = repo / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    (work / 'strict_affine.py').write_bytes(strict_source.read_bytes())
    sys.modules['cost_search'] = SimpleNamespace()
    strict = load('permutation252_lazy_context_strict', work / 'strict_affine.py')
    prog = repo / 'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    text = prog.read_text().split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', text)
    assert len(nodes) == 6459
    cases = []

    def visit(q, prefix):
        for b, e in enumerate(nodes[q]):
            path = prefix + str(b)
            op, *arg = e.split()
            if op == 'CN':
                visit(int(arg[0]), path)
                continue
            register = int(arg[0]) if arg else None
            for zero in ((True, False) if op == 'CD' else (None,)):
                physical = audit.NEWPHYS[register] if op in ('CI', 'CD') else register
                branch = (physical, zero) if op == 'CD' else None
                successor = audit.successor(path, op, register, zero)
                effect = ('inc', physical) if op == 'CI' else ('dec', physical) if op == 'CD' and not zero else None
                right = [('b', int(c)) for c in successor] if successor is not None else []
                right += [('r', 0, 1, (41 if successor is None else 40) - len(successor or '')),
                          ('b', 1), ('box', ('plain', effect))]
                cases.append((path, op, register, zero, branch, strict.canon([('b', 1)], right)))

    visit(0, '')
    assert len(cases) == 8391

    def check(current, index):
        path, op, register, zero, branch, target = cases[index]
        try:
            rules, literal = strict.run(current, path, branch, target, halt=op == 'CH', fuel=args.affine_fuel)
            assert literal > 0
            return True, sum(rules.values()), None
        except AssertionError as exc:
            return False, 0, 'fuel' if str(exc) == 'symbolic fuel exhausted' else 'unsupported_symbolic_rule'
        except KeyError:
            return False, 0, 'missing_transition'

    omitted = {8202,8203,8204,8358,8359,8360} if args.exclude_phase_guards else set()
    included = [i for i in range(len(cases)) if i not in omitted]
    began = time.monotonic()
    usage = defaultdict(set)
    baseline_cost = {}
    for index in included:
        traced = Tracking(table)
        ok, cost, _ = check(traced, index)
        assert ok, ('baseline_case', index)
        baseline_cost[index] = cost
        for row in traced.used:
            usage[row].add(index)
    target_spares = [0] * 65
    target_spares[8] = 1
    target_ones = audit.paint('', 40, [0] * 9, target_spares, 2)
    q, h, ones, _, _ = audit.run_prefix(numeric, 82552)
    assert (q, h, ones) == (96, 2, target_ones)
    protected_targets = {table[k][2] for k in protected}
    eligible = [q for q in states if q not in {'64', '96'} and q not in protected_targets
                and all((q, b) not in protected for b in (0, 1))]
    incoming = {q: sorted([k for k, (_, _, t) in table.items() if t == q and k[0] != q],
                          key=lambda k: (int(k[0]), k[1])) for q in eligible}
    family = [q for q in eligible if len(incoming[q]) == 2]
    assert len(family) == 46 and all(usage[k] for q in family for k in incoming[q])
    # old107's two distinct guards motivated the previous public253 experiment.
    family.sort(key=lambda q: (q != '107', int(q)))
    if args.deletions: family = [q for q in family if q in args.deletions.split(',')]
    out = args.output.resolve();out.parent.mkdir(parents=True,exist_ok=True)
    # No rewritten row in this exact family has source96; both literal
    # dispatch rows really are fixed, not merely its state label.
    assert all(k[0] != '96' for dead in family for k in incoming[dead])
    ordered = lambda indices: sorted(indices,key=lambda i:(baseline_cost[i],i))
    affected = {dead:ordered(set.union(*(usage[k] for k in incoming[dead]))) for dead in family}
    destinations = {dead:[(w,d,q) for w in (0,1) for d in ('L','R') for q in states+['254'] if q != dead] for dead in family}
    stack = [(dead,{}) for dead in reversed(family)]
    groups = {dead:{'deleted_old':int(dead),'incoming_rows':[list(k) for k in incoming[dead]],
                    'planned_joint_assignments':1008**2,'partial_nodes_evaluated':0,
                    'symbolic_checks':0,'pruned_completions':0,'survivors':0} for dead in family}
    result = {'status':'running','scope':'Finite lazy two-incoming full-action 251-state diagnostics; no kernel proof of modified tables, minimality or consistency claim. Optional guard filter depends on an original-source phase invariant.',
      'attribution':'Mira-Cult/Jeff/Wade original254; mira-emmy public253 PR20; frozen original-logic permutation252; source27 strict affine executor.',
      'table_sha256':audit.EXPECTED_SHA,'logical_to_physical':list(audit.NEWPHYS),
      'protected_pairs':55,'fixed_literal_dispatch_pairs':[[96,0],[96,1]],'fixed_blank_start':64,
      'baseline8391':'PASS','baseline_exact82552_whole_boot':'PASS',
      'planned_joint_assignments':len(family)*1008**2,'eligible_deletions':list(map(int,family)),
      'branch_rule':'Intercept an unassigned incoming-row lookup BEFORE returning its row. Restart each branch from the original case source; no symbolic state continuation is assumed.',
      'prune_rule':'A deterministic failure that reads no unassigned row applies to every completion. This concerns the finite strict checker, not semantic impossibility.',
      'compensating_changes_included':True,'entry_full_action_choices':True,'excluded_phase_cases':sorted(omitted),'affine_fuel':args.affine_fuel,'seconds_limit':args.seconds,
      'boot_limit':args.boot_limit,'command':[sys.executable,*sys.argv],
      'python':platform.python_version(),'scratch':str(work),'partial_nodes_evaluated':0,
      'affine_checks':0,'full_recheck_affine_checks':0,'pruned_completions':0,
      'affine_survivors':[],'whole_boot_survivors':[],'states':list(groups.values()),
      'input_sha256':{'driver':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      'context_helper':hashlib.sha256((base/'permutation252_context_search.py').read_bytes()).hexdigest(),
                      'audit_helper':hashlib.sha256((base/'candidate252_independent_audit.py').read_bytes()).hexdigest(),
                      'strict_executor':hashlib.sha256(strict_source.read_bytes()).hexdigest(),
                      'Prog254':hashlib.sha256(prog.read_bytes()).hexdigest()}}
    failures=Counter()
    def weight(assign): return 1008**(2-len(assign))
    def save():
        result['elapsed_seconds']=time.monotonic()-began
        result['failure_reasons']=dict(failures)
        result['remaining_frontier']=[{'deleted_old':int(dead),'assigned_targets':{str(i):[q[0],q[1],int(q[2])] for i,q in assign.items()},
                                       'joint_completions':weight(assign)} for dead,assign in reversed(stack)]
        result['remaining_joint_assignments']=sum(weight(assign) for dead,assign in stack)
        assert result['planned_joint_assignments']==result['pruned_completions']+len(result['affine_survivors'])+result['remaining_joint_assignments']
        out.write_text(json.dumps(result,indent=2)+'\n')
    def blank_run(current):
        state,head,tape='64',0,set()
        for tick in range(args.boot_limit+1):
            if (state,head,tape)==('96',2,target_ones):return {'outcome':'exact_frozen_whole_frame','steps':tick}
            if state=='254':return {'outcome':'halt','steps':tick}
            if tick==args.boot_limit:return {'outcome':'fuel_limit','steps':tick}
            write,direction,state=current[state,int(head in tape)]
            if write:tape.add(head)
            else:tape.discard(head)
            head+=1 if direction=='R' else -1
    print('BASELINE8391+82552 PASS; lazy family',result['planned_joint_assignments'],flush=True)
    save();journal=work/'lazy-nodes.jsonl'
    with journal.open('w') as record:
        while stack:
            if time.monotonic()-began>=args.seconds:break
            dead,assign=stack.pop();group=groups[dead];row_keys=incoming[dead]
            current={k:v for k,v in table.items() if k[0]!=dead}
            for index,destination in assign.items():
                key=row_keys[index];current[key]=destination
            pending={row_keys[index]:index for index in range(2) if index not in assign}
            current=PartialTable(current,pending)
            assert all(current[k]==table[k] for k in protected)
            # Access the raw dict to avoid deliberately intercepting pending rows
            # while checking the protected literal dispatcher.
            assert all(dict.__getitem__(current,('96',b))==table['96',b] for b in (0,1))
            failed=reason=needed=None;checks=0
            try:
                for index in affected[dead]:
                    ok,_,reason=check(current,index);checks+=1;result['affine_checks']+=1
                    if not ok:failed=index;break
                if failed is None:
                    for index in included:
                        ok,_,reason=check(current,index);checks+=1;result['full_recheck_affine_checks']+=1
                        if not ok:failed=index;break
            except NeedTarget as request:needed=request.index
            result['partial_nodes_evaluated']+=1;group['partial_nodes_evaluated']+=1;group['symbolic_checks']+=checks
            entry={'deleted_old':int(dead),'assigned_targets':{str(i):[q[0],q[1],int(q[2])] for i,q in assign.items()}}
            if needed is not None:
                assert needed not in assign
                entry.update({'outcome':'branch','incoming_index':needed})
                for destination in reversed(destinations[dead]):
                    stack.append((dead,{**assign,needed:destination}))
            elif failed is not None:
                count=weight(assign);group['pruned_completions']+=count;result['pruned_completions']+=count
                failures[reason]+=1
                entry.update({'outcome':'prune','first_failure_case':failed,'reason':reason,'joint_completions':count})
            elif len(assign)<2:
                # No tested trace uses this row, but blank initialization may;
                # materialize every remaining choice before any blank claim.
                needed=next(i for i in range(2) if i not in assign)
                entry.update({'outcome':'branch_unused_in_runtime','incoming_index':needed})
                for destination in reversed(destinations[dead]):stack.append((dead,{**assign,needed:destination}))
            else:
                assert len(current)==502 and all(t!=dead for _,_,t in current.values())
                data=('#! start 64\n'+''.join(f'{q} {b} {v} {d} {t}\n' for(q,b),(v,d,t) in sorted(current.items(),key=lambda item:(int(item[0][0]),item[0][1])))).encode()
                path=work/f'lazy_{dead}_{assign[0]}_{assign[1]}.tm';path.write_bytes(data)
                entry.update({'outcome':'affine_survivor','table':str(path),'sha256':hashlib.sha256(data).hexdigest(),'boot':blank_run(current)})
                result['affine_survivors'].append(entry);group['survivors']+=1
                if entry['boot']['outcome']=='exact_frozen_whole_frame':result['whole_boot_survivors'].append(entry)
                print('SURVIVOR',json.dumps(entry),flush=True)
            record.write(json.dumps(entry,separators=(',',':'))+'\n')
            if result['partial_nodes_evaluated']%1000==0:record.flush();save()
    result['status']='completed' if not stack else 'time_bound_partial'
    result['journal']={'path':str(journal),'bytes':journal.stat().st_size,'sha256':hashlib.sha256(journal.read_bytes()).hexdigest()}
    save();print(json.dumps({k:result[k] for k in ('status','partial_nodes_evaluated','pruned_completions','remaining_joint_assignments','affine_survivors','elapsed_seconds')}),flush=True)

if __name__=='__main__':main()

