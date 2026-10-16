#!/usr/bin/env python3
"""Test the PR20 four-row initializer change on source09's decoder256.

This is an executable engineering experiment, not a kernel-checked proof.
The source09 affine checker runs unchanged on a scratch copy. Its protected
register-box contract is checked before it is used. All inputs are bundled; no network access or repository checkout is required.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

if not __debug__:
    raise SystemExit("Run without -O/-OO: executable certificates require assertions")


def prepare(vendor, work):
    provenance = json.loads((vendor / 'PROVENANCE.json').read_text())
    for rel in ('verify.py','vendor/tmlib.py','vendor/symexec.py',
                'machines/baseline254.tm','machines/decoder256.tm','data/candidate202.json'):
        source = vendor / rel
        assert hashlib.sha256(source.read_bytes()).hexdigest() == provenance['files_sha256'][rel], ('vendor source mismatch', rel)
        target = work / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    spec = importlib.util.spec_from_file_location('source09_machine_verify', work / 'verify.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def inc(p):
    k = len(p) - 1
    while k >= 0 and p[k] == '1':
        k -= 1
    return '' if k < 0 else p[:k] + '1' + '0' * (len(p) - 1 - k)


def strip(p, b, k):
    while p and k:
        k -= p[-1] == b
        p = p[:-1]
    return p


def step_rm(obj, conf):
    pc, regs = conf
    q, path = obj['root'], ''
    while True:
        bit = int(pc[len(path)]) if len(path) < len(pc) else 0
        path += str(bit)
        e = obj['nodes'][str(q)][bit]
        if e[0] != 'N':
            break
        q = e[1]
    reg = list(regs)
    op = e[0]
    if op == 'I':
        reg[e[1]] += 1
        successor = inc(path)
    elif op == 'D':
        if reg[e[1]]:
            reg[e[1]] -= 1
            successor = inc(path)
        else:
            successor = inc(strip(path, '0', 1))
    elif op == 'B':
        successor = inc(strip(path, '0', e[1]))
    elif op == 'C':
        successor = strip(path, '1', e[1])
    else:
        return None
    return successor.rstrip('0'), tuple(reg)


def frame(run, depth=35):
    tape, head = run.tape, run.head
    ones = {x for x, b in tape.items() if b}
    if head - 1 not in ones or any(x < head - 1 for x in ones):
        return None
    candidates = [x for x in ones if x >= head + depth]
    if not candidates:
        return None
    header = min(candidates)
    pc = ''.join('1' if head+i in ones else '0' for i in range(depth)).rstrip('0')
    x, values = header + 1, []
    while x not in ones and x + 1 in ones:
        x += 1
        n = 0
        while x in ones:
            x += 1
            n += 1
        values.append(n - 1)
    if len(values) < 9 or any(y >= x for y in ones):
        return None
    regs = [0]*9
    for i, j in enumerate((2,4,3,7,6,8,0,1,5)):
        regs[j] = values[i]
    return {'pc': pc, 'logical_registers': regs, 'gap': header-head,
            'head': head, 'state': run.state, 'steps': run.t,
            'spare_blocks': len(values)-9,
            'spare_nonzero': [(i,v) for i,v in enumerate(values[9:]) if v],
            'ones_relative': sorted(x-head for x in ones)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--vendor', type=Path, default=Path(__file__).resolve().parents[1] / 'vendor/decoder255')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--fuel', type=int, default=3000000)
    args = parser.parse_args()
    args.output = args.output or Path(tempfile.mkdtemp(prefix="decoder255-replay-"))
    args.output.mkdir(parents=True, exist_ok=True)
    checker = prepare(args.vendor, args.output / '_source09')
    source, _ = checker.load(args.output / '_source09/machines/decoder256.tm')
    table = source.copy()
    delta = {('3',0):(0,'L','48'), ('5',0):(1,'R','97'),
             ('5',1):(1,'R','64'), ('49',1):(0,'R','5')}
    for key, val in delta.items():
        assert table[key] != val, ('already changed', key)
        table[key] = val
    table = {k: v for k,v in table.items() if k[0] != '8'}
    assert all(v[2] != '8' for v in table.values())
    count = checker.check_total_closed(table, '5')
    assert count == 255
    reachable, pending = set(), ['5']
    while pending:
        q = pending.pop()
        if q in reachable or q == '254':
            continue
        reachable.add(q)
        pending.extend(table[q, b][2] for b in (0, 1))
    assert len(reachable) == count, 'unreachable working-state labels'
    text = '#! start 5\n' + ''.join(
        f'{q} {b} {w} {d} {target}\n'
        for (q,b),(w,d,target) in sorted(table.items(), key=lambda kv:(int(kv[0][0]),kv[0][1])))
    (args.output / 'decoder255_bootshare.tm').write_text(text)
    labels = ['5'] + sorted(({q for q,_ in table} - {'5'}), key=int)
    compact = {q: str(i) for i,q in enumerate(labels)} | {'254':'255'}
    standard = '#! start 0\n' + ''.join(
        f'{compact[q]} {b} {w} {d} {compact[target]}\n'
        for q in labels for b in (0,1)
        for w,d,target in [table[q,b]])
    (args.output / 'decoder255.tm').write_text(standard)
    (args.output / 'old_to_compact.json').write_text(json.dumps(compact,indent=2)+'\n')
    paths = checker.paths_from_dag('candidate202.json')
    result = {'status':'engineering experiment; no new kernel verification',
              'working_states':count, 'rows':len(table), 'start':5, 'halt':254,
              'machine_sha256':hashlib.sha256(text.encode()).hexdigest(),
              'normalized_machine_sha256':hashlib.sha256(standard.encode()).hexdigest(),
              'normalized_start':0,'normalized_halt':255,
              'delta_from_source09_decoder256':{f'{q}/{b}':list(v) for (q,b),v in delta.items()},
              'deleted_state':8}
    try:
        stats, used = checker.affine_audit(table, paths, 41)
        result['affine'] = stats
        result['explicit_read_pairs'] = len(used)
        result['protected_box_pairs'] = len(checker.BOX_PAIRS)
        print('Affine audit:', stats, flush=True)
    except Exception as e:
        result['affine_failure'] = repr(e)
        print('Affine audit FAIL:', repr(e), flush=True)
        raise
    obj = json.loads((args.output / '_source09/data/candidate202.json').read_text())
    expected = ('', (2,0,0,0,0,0,0,0,0))
    rm_index = 0
    run = checker.Run(table, '5')
    init = None
    matched = []
    while run.t <= args.fuel:
        if run.state == '96':
            f = frame(run)
            if f:
                got = (f['pc'], tuple(f['logical_registers']))
                if init is None:
                    if got == expected:
                        init = f
                        matched.append(f | {'rm_steps':0})
                        print('First exact initial register frame:', f['steps'],f['gap'],flush=True)
                        expected = step_rm(obj, expected)
                        rm_index += 1
                elif got == expected:
                    if f['gap'] >= 41:
                        result['boot_success'] = f | {'rm_steps':rm_index,
                            'encountered_every_successive_rm_configuration':True}
                        print('Admissible frame:',f['steps'],f['gap'],rm_index,flush=True)
                        break
                    expected = step_rm(obj, expected)
                    rm_index += 1
                    if len(matched) < 12:
                        matched.append(f | {'rm_steps':rm_index-1})
        if run.t == args.fuel:
            break
        if not run.step():
            result['unexpected_halt'] = {'steps':run.t, 'state':run.state}
            break
    assert result.get('boot_success', {}).get('steps') == 606702, 'required exact boot endpoint was not reached'
    assert result['boot_success']['rm_steps'] == 676
    assert result['normalized_machine_sha256'] == 'f4aad63fe10699100aa48a0da22bb4582f76d641e9f8a0c3d9123055d066b29f'
    result['first_initial_frame'] = init
    result['matched_prefix_examples'] = matched
    result['final_diagnostic'] = {'steps':run.t, 'state':run.state,'head':run.head,
                                'matched_rm_steps':rm_index if 'boot_success' in result else rm_index-1,
                                'fuel':args.fuel}
    (args.output / 'transfer_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Output directory:', args.output.resolve(), flush=True)
    print(json.dumps({k:v for k,v in result.items() if k not in ('matched_prefix_examples','first_initial_frame','boot_success')},indent=2))


if __name__ == '__main__':
    main()
