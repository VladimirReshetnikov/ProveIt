#!/usr/bin/env python3
"""Replay bounded quotient searches on the combined experimental 197 table."""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from zipfile import ZipFile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[6]
COMBINED = HERE.parents[1] / 'source-search' / 'negation-mp197'
ARCHIVE = REPO / 'docs/incoming/pa_consistency_research_2026-11-13.zip'
PINS = {
    ARCHIVE: '466c804d54495d3347252a98788af021aecc459b041fcc1733b3adf1ff1e943b',
    COMBINED / 'machine.native.tm': 'a2db6b2791912d90cb87b6b310157180917c5652d85ecb09a506e0de1628a264',
    COMBINED / 'source.tree.json': '7d01a47445daf5ff804d32af8886364b3ee9e9f38efaa1e9d147d7989c28479e',
}
CONTEXT_SHA = '590282dae1a5bc9d6e3deca70ec0622b0b3ce0397e703c7bdd2cf11277f9184e'
PROTECTED_SHA = '6716848059a0a69d1c75f40703ee84e6e22505868c05a56dbbd26a8d639fe1c3'
SAMPLE_SHA = 'a76ed02baa5b8022d216c6b44e7942c054e4a0acc363b4b1f446fafcd8502294'
EXPECTED = {'inherited_or_one_synthesized': 45745616, 'left_left': 561872416,
            'wide_0': 1072728384, 'wide_1': 1430304512,
            'wide_2': 1430304512, 'wide_3': 1430304512}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(argv):
    return subprocess.run([str(x) for x in argv], check=True, capture_output=True, text=True)


def expand(xs, k):
    out = []
    for t in xs:
        if t[0] == 'b':
            out.append(t[1])
        elif t[0] == 'r':
            out.extend([t[1]] * min(k-len(out), t[3]))
            if t[2] and len(out) < k:
                return tuple(out + [-1] * (k-len(out)))
        else:
            out.append(0)
            return tuple((out + [-1] * k)[:k])
        if len(out) >= k:
            return tuple(out[:k])
    return tuple(out + [0] * (k-len(out)))


def replace_once(source, old, new):
    need(source.count(old) == 1, f'cannot patch search source: {old!r}')
    return source.replace(old, new)


def main():
    need(__debug__, 'the inherited symbolic executor requires Python assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    for path, expected in PINS.items():
        need(digest(path) == expected, f'input hash mismatch: {path}')
    with tempfile.TemporaryDirectory(prefix='combined197-quotients-') as d:
        temp = Path(d)
        with ZipFile(ARCHIVE) as z:
            for item in z.infolist():
                dest = (temp / item.filename).resolve()
                need(dest.is_relative_to(temp), f'unsafe archive path: {item.filename}')
            z.extractall(temp)
        archive = temp / 'pa_consistency_research'
        sys.path.insert(0, str(archive / 'verification'))
        import check
        symbolic = check.s
        machine = check.parse(COMBINED / 'machine.native.tm')
        tree = check.tuplify(json.loads((COMBINED / 'source.tree.json').read_text()))
        check.set_tree(tree)
        need(len(machine) == 394 and len(symbolic.SITES) == 3573 and len(symbolic.CASES) == 4641,
             'unexpected machine or source census')
        ctx = defaultdict(set)
        def observe(conf):
            q, on, left, right = conf
            ctx[q, right[0][1]].add(tuple(reversed(expand(left, 7))) + expand(right, 3))
        for case in symbolic.CASES:
            need(symbolic.run_case(machine, case, observe)[0], f'baseline symbolic failure {case[:2]}')
        need(check.startup(machine) == 58154, 'baseline startup changed')
        tape = set(); q = 74; pos = 0; startup_states = set()
        for _ in range(58154):
            b = int(pos in tape); startup_states.add(q)
            ctx[q,b].add(tuple(int(pos+j in tape) for j in range(-7,3)))
            write, direction, q = machine[q,b]
            tape.discard(pos)
            if write:
                tape.add(pos)
            pos += 1 if direction == 'R' else -1
        need(q == 84 and len(startup_states) == 123, 'unexpected startup census')
        labels = sorted({q for q,b in machine}); indices = {q:i for i,q in enumerate(labels)}
        indices[254] = len(labels)
        need(len(labels) == 197 and sum(map(len,ctx.values())) == 12759, 'context census changed')
        def make_context_file(path, extra_protected):
            lines = [f'{len(labels)} 7 3']
            protected = check.BOX | {84} | extra_protected
            for q in labels:
                lines.append(f'{q} {int(q in protected)}')
                for b in (0,1):
                    w,d,z = machine[q,b]; contexts = sorted(ctx[q,b])
                    lines.append(f'{w} {1 if d == "R" else -1} {indices[z]} {len(contexts)}')
                    lines.extend(' '.join(map(str,c)) for c in contexts)
            path.write_text('\n'.join(lines)+'\n', encoding='ascii')
        context = temp / 'contexts.txt'; protected_context = temp / 'startup-protected.txt'
        make_context_file(context,set()); make_context_file(protected_context,startup_states)
        need(digest(context) == CONTEXT_SHA and digest(protected_context) == PROTECTED_SHA,
             'context encoding differs')
        src = archive / 'verification/search'
        bins = {}
        for name in ('recursive_fold','recursive_two','recursive_wide'):
            bins[name] = temp / name
            command(['g++','-O3','-std=c++17',src/(name+'.cpp'),'-o',bins[name]])
        jobs = [('inherited_or_one_synthesized','recursive_fold',['extended']),
                ('left_left','recursive_two',[])]
        jobs += [(f'wide_{i}','recursive_wide',[str(i)]) for i in range(4)]
        def run_job(job):
            name, binary, options = job
            out = temp / (name+'.hits')
            result = command([bins[binary], context, out, *options])
            match = re.search(r'done candidates (\d+) hits (\d+) seconds ', result.stderr)
            need(match is not None, f'missing final count for {name}')
            count, hits = map(int, match.groups())
            need(count == EXPECTED[name] and hits == 0 and out.read_text() == '',
                 f'changed quotient result for {name}: {count}, {hits}')
            return name, count
        with ThreadPoolExecutor(max_workers=6) as pool:
            counts = dict(pool.map(run_job,jobs))
        # Sample near-misses: do not discard an exit or unknown read during
        # candidate generation, then check each resulting candidate using the
        # original full symbolic executor. This is deliberately not exhaustive.
        source = (src/'recursive_fold.cpp').read_text()
        source = replace_once(source,
            'if(h<0||h>=K||state>=NN)return false;\n   int bit=tape[h];if(bit<0)return false;',
            'if(state>=NN)return false;\n   if(h<0||h>=K)return true;\n   int bit=tape[h];if(bit<0)return true;')
        source = replace_once(source, '   if(blocked)continue;\n   for(int synth',
                              '   if(blocked)continue;\n   int pairhits=0, pairtotal=0;\n   for(int synth')
        source = replace_once(source, '      hits++;\n      out<<',
                              '      pairtotal++; if(pairtotal%30) continue; pairhits++;\n      hits++;\n      out<<')
        source = replace_once(source, "out<<'\\n';out.flush();",
                              "out<<'\\n';out.flush();if(hits>=2000){cerr<<\"CAP 2000\\n\";return 0;}")
        source = replace_once(source, "      cerr<<'\\n';\n     }",
                              "      cerr<<'\\n';\n      if(pairhits>=1)goto pair_done;\n     }")
        source = replace_once(source, '   }\n  }\n }\n cerr<<"done candidates',
                              '   }\n   pair_done:;\n  }\n }\n cerr<<"done candidates')
        optimistic_source = temp/'optimistic.cpp'; optimistic_source.write_text(source)
        optimistic = temp/'optimistic'; command(['g++','-O3','-std=c++17',optimistic_source,'-o',optimistic])
        sample = temp/'sample.txt'; command([optimistic,protected_context,sample,'extended'])
        need(digest(sample) == SAMPLE_SHA, 'sample selection changed')
        rows = sample.read_text().splitlines()
        pairs = {tuple(map(int, row.split()[:2])) for row in rows}
        need(len(rows) == len(pairs) == 2000, 'sample pair census changed')
        # Prioritize source cases whose *baseline* path uses either merged state.
        # No correctness claim depends on that prioritization: each candidate is
        # rejected only by a failed concrete call to the symbolic executor, and
        # a survivor would get the full all-case checker.
        by_state = defaultdict(set); original_step = symbolic.sstep; current = 0
        def observed(m, br, conf, visit=None):
            by_state[conf[0]].add(current)
            return original_step(m,br,conf,visit)
        symbolic.sstep = observed
        try:
            for current, case in enumerate(symbolic.CASES):
                need(symbolic.run_case(machine,case)[0], f'baseline failure {current}')
        finally:
            symbolic.sstep = original_step
        rejected = Counter(); need_full = 0
        for line in rows:
            a,z,w0,d0,n0,w1,d1,n1 = map(int,line.split())
            candidate = {(q,b):(w,d,a if target == z else target)
                         for (q,b),(w,d,target) in machine.items() if q != z}
            candidate[a,0] = (w0,'R' if d0 == 1 else 'L',a if n0 == z else n0)
            candidate[a,1] = (w1,'R' if d1 == 1 else 'L',a if n1 == z else n1)
            for ci in sorted(by_state[a] | by_state[z]):
                case = symbolic.CASES[ci]
                if not symbolic.run_case(candidate,case)[0]:
                    rejected[str(case[0])] += 1
                    break
            else:
                need_full += 1
                ok, detail = symbolic.validate(candidate)
                need(not ok, f'potential candidate found: {line} {detail}')
                rejected['full_'+str(detail[0])] += 1
        need(sum(rejected.values()) == 2000, 'not every sampled candidate failed')
        result = {'archive_sha256':PINS[ARCHIVE], 'table_sha256':PINS[COMBINED/'machine.native.tm'],
                  'source_tree_sha256':PINS[COMBINED/'source.tree.json'],
                  'working_states':197, 'source_sites':3573, 'symbolic_cases':4641,
                  'startup_steps':58154, 'startup_distinct_states':123,
                  'partial_window_contexts':12759, 'contexts_sha256':CONTEXT_SHA,
                  'startup_protected_contexts_sha256':PROTECTED_SHA,
                  'protected_search_counts':counts, 'protected_search_hits':0,
                  'optimistic_sample_sha256':SAMPLE_SHA, 'optimistic_sample_candidates':2000,
                  'optimistic_sample_full_checks_required':need_full,
                  'optimistic_sample_first_failed_sites':dict(sorted(rejected.items())),
                  'scope':'Finite protected local searches plus a non-exhaustive sample. '
                          'No smaller machine, PA theorem, or state lower bound follows.'}
        data = json.dumps(result,indent=2,sort_keys=True)+'\n'
        print(data,end='')
        if args.output:
            args.output.write_text(data)


if __name__ == '__main__':
    main()
