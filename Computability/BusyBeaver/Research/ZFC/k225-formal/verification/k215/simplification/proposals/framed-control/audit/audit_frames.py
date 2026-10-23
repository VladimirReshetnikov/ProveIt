#!/usr/bin/env python3
"""Independent K215 residual-frame extraction from maintained source files.

No received script is imported or executed. This is finite engineering evidence,
not a proof assistant. In particular it does not prove the framing lemma,
decoder execution, source-action append laws, or the machine-to-ZFC endpoint.
"""
from __future__ import annotations

import argparse
import collections
import copy
import hashlib
import json
import re
from pathlib import Path


def require(p, msg):
    if not p:
        raise ValueError(msg)


def read_json(p):
    return json.loads(p.read_text())


def immutable(x):
    return tuple(immutable(v) for v in x) if isinstance(x, list) else x


def parse_table(text):
    body = text.split('def table215 : List (Row × Row) := [', 1)[1].split('\n]\n', 1)[0]
    toks = re.findall(r'none|some \((?:true|false), (?:true|false), \d+\)', body)
    require(len(toks) % 2 == 0, 'Odd number of table entries')
    tab = {}
    for index, tok in enumerate(toks):
        if tok == 'none':
            continue
        w, d, q = re.fullmatch(r'some \((true|false), (true|false), (\d+)\)', tok).groups()
        tab[index // 2, index % 2] = (int(w == 'true'), d == 'true', int(q))
    require(len(tab) == 430, 'Table must have all 430 working actions')
    return tab


def parse_decoder(text):
    nb = text.split('def sourceNodes : Array Node := #[', 1)[1].split('\n]\n', 1)[0]
    nodes = [(kind, int(a), int(b)) for kind, a, b in re.findall(r'\.(leaf|fork) (\d+) (\d+)', nb)]
    rb = text.split('def roles : Array Role := #[', 1)[1].split('\n]\n', 1)[0]
    roles = []
    for line in rb.splitlines():
        if not line.strip():
            continue
        m = re.fullmatch(r'\s*⟨(\d+), (\d+), \[([^]]*)\], (.*)⟩,?\s*', line)
        require(m is not None, 'Unparsed decoder role: ' + line)
        n, q, ctx, edge_text = m.groups()
        edges = []
        er = r'\(\.internal (\d+) (\d+)\)|\(\.primitive (\d+) ⟨(true|false), (\(?-?1\)?), (\d+)⟩\)'
        for e in re.finditer(er, edge_text):
            a, b, leaf, w, direction, target = e.groups()
            edges.append(('i', int(a), int(b)) if a is not None else
                         ('p', int(leaf), (int(w == 'true'), int(direction.strip('()')) == 1, int(target))))
        require(len(edges) == 2, 'Role must have two edges')
        roles.append((int(n), int(q), tuple(int(s.strip() == 'true') for s in ctx.split(',') if s.strip()), edges))
    root = int(re.search(r'def sourceRoot : Nat := (\d+)', text).group(1))
    require((len(nodes), len(roles)) == (202, 234), 'Unexpected decoder dimensions')
    return nodes, roles, root


def bind_sites(nodes, roles, root, table, sites):
    op_names = {0: 'CI', 1: 'CD', 2: 'CB', 3: 'CC', 4: 'CH'}
    expanded = []
    def visit(n, path):
        kind, a, b = nodes[n]
        if kind == 'leaf':
            expanded.append([path, op_names[a], None if a == 4 else b])
        else:
            require(a < n and b < n, 'Source DAG must be acyclic in listed order')
            visit(a, path + '0')
            visit(b, path + '1')
    visit(root, '')
    require(expanded == sites, 'Candidate source sites differ from exact current decoder expansion')
    ports = {}
    for word, op, arg in sites:
        rid, node, history = 0, root, (1,)
        for j, char in enumerate(word):
            rn, q, context, edges = roles[rid]
            require(rn == node and context == history[-2:], 'Role/node/history mismatch')
            require(nodes[node][0] == 'fork', 'Expected an internal source node')
            b = int(char)
            edge = edges[b]
            child = nodes[node][1 + b]
            if j == len(word) - 1:
                require(edge[0] == 'p' and edge[1] == child, 'Final source edge must be primitive')
                require(table[q, b] == edge[2], 'Primitive role disagrees with current table')
                ports[word] = q
            else:
                require(edge[0] == 'i', 'Premature primitive source edge')
                rid, node = edge[1], child
                history += (b,)
    return ports


def step(table, s):
    """Exact sstep fragment used by control templates, branch=None.

    Any arithmetic oracle event is rejected. Control-family traces use only
    literal table rows, reorientation, runs and the box-left boundary row.
    """
    q, on_left, left, right = s
    if on_left:
        if not left:
            return (q, False, (), (('b', 0),) + right), False, 'empty-left'
        x, rest = left[0], left[1:]
        if x[0] == 'b':
            return (q, False, rest, (x,) + right), False, 'reorient'
        if x[0] == 'x':
            return None
        _, b, a, c = x
        row = table.get((q, b))
        if row is not None and row[1] is False and row[2] == q:
            return (q, True, rest, (('r', row[0], a, c),) + right), False, 'run-left'
        if c:
            return (q, True, (('b', b), ('r', b, a, c - 1)) + rest, right), False, 'peel-left'
        if a == 0:
            return (q, True, rest, right), False, 'peel-zero-left'
        return None
    if not right:
        return None
    x, rest = right[0], right[1:]
    if x[0] == 'b':
        row = table.get((q, x[1]))
        if row is None:
            return None
        w, d, target = row
        return ((target, False, (('b', w),) + left, rest) if d else
                (target, True, left, (('b', w),) + rest)), True, 'literal'
    if x[0] == 'r':
        _, b, a, c = x
        row = table.get((q, b))
        if row is not None and row[1] is True and row[2] == q:
            return (q, False, (('r', row[0], a, c),) + left, rest), False, 'run-right'
        if c:
            return (q, False, left, (('b', b), ('r', b, a, c - 1)) + rest), False, 'peel-right'
        if a == 0:
            return (q, False, left, rest), False, 'peel-zero-right'
        return None
    require(x[0] == 'x', 'Unknown segment')
    if rest or x != ('x', 'none', 0):
        return None
    # These states would trigger the existing arithmetic oracle, not the literal fallback.
    if q in (51, 36, 25, 48, 32, 33, 22, 55, 60):
        return None
    row = table.get((q, 0))
    if row is not None and row[0] == 0 and row[1] is False:
        return (row[2], True, left, right), True, 'box-left'
    return None


def normalized_segments(xs):
    """Exact polynomial run lengths, merging equal adjacent bit runs."""
    out = []
    for x in xs:
        y = ('r', x[1], 0, 1) if x[0] == 'b' else tuple(x)
        if y[0] == 'r' and y[2:] == (0, 0):
            continue
        if out and y[0] == 'r' and out[-1][0] == 'r' and y[1] == out[-1][1]:
            z = out[-1]
            out[-1] = ('r', y[1], y[2] + z[2], y[3] + z[3])
        else:
            out.append(y)
    return tuple(out)


def strip(word, bit, count):
    i = len(word)
    while count and i:
        i -= 1
        count -= word[i] == bit
    return word[:i]


def increment(word):
    if not word or all(b == '1' for b in word):
        return '0' * len(word), True
    i = word.rfind('0')
    return word[:i] + '1' + '0' * (len(word) - i - 1), False


def action(word, op, arg):
    if op == 'CC':
        return strip(word, '1', arg), False
    return increment(strip(word, '0', arg))


def source_frame_ok(suffix, op, arg):
    result, overflow = action(suffix, op, arg)
    return suffix.count('1' if op == 'CC' else '0') >= arg and not overflow, result


def word_scan(table, q, word):
    """Check LeftWord table premises, including final marker."""
    for b in map(int, word):
        row = table.get((q, b))
        if row is None or row[0] != b or row[1] is not False:
            return None
        q = row[2]
    return q


def word_scan_rows(table, q, word):
    rows = []
    for b in map(int, word):
        row = table.get((q, b))
        require(row is not None and row[0] == b and row[1] is False, 'Invalid LeftWord row')
        rows.append([q, b, row[2]])
        q = row[2]
    require(q == 2, 'Return scanner does not finish at state 2')
    return rows


def local_trace(table, q, suffix, allowed):
    start = q, False, tuple(('b', int(b)) for b in suffix[:-1][::-1]), (
        ('b', int(suffix[-1])), ('r', 0, 1, 16), ('b', 1), ('x', 'none', 0))
    s, trace = start, []
    for _ in range(300):
        if s[1] and not s[2]:
            return (start, s, trace) if s[0] in allowed else None
        result = step(table, s)
        if result is None:
            return None
        t, moved, kind = result
        trace.append({'before': s, 'after': t, 'moved': moved, 'kind': kind})
        s = t
    return None


def discover(table, sites, ports, allowed):
    templates, by_key, records, fallback = [], {}, [], []
    for i, (word, op, arg) in enumerate(sites):
        if op not in ('CC', 'CB'):
            continue
        full_result, overflow = action(word, op, arg)
        found = None
        for cut in range(len(word) - 1, 0, -1):
            prefix, suffix = word[:cut], word[cut:]
            ok, result = source_frame_ok(suffix, op, arg)
            if not ok or overflow or full_result != prefix + result:
                continue
            key = (ports[word], suffix, op, arg, result)
            trace = local_trace(table, ports[word], suffix, allowed)
            if trace is None:
                continue
            start, final, steps = trace
            if word_scan(table, final[0], prefix[::-1] + '1') != 2:
                continue
            expected = tuple(('b', int(b)) for b in result) + (
                ('r', 0, 1, 16 + len(suffix) - len(result)), ('b', 1), ('x', 'none', 0))
            if normalized_segments(final[3]) != normalized_segments(expected):
                continue
            if key not in by_key:
                tid = len(templates)
                by_key[key] = tid
                templates.append(dict(id=tid, key=[True, ports[word], suffix, op, arg, False, result, 0, 0,
                                                   len(suffix) - len(result)], start=start, pre_home=final,
                                      steps=len(steps), trace=steps, return_state=final[0]))
            found = dict(site=i, pc=word, cut=cut, template=by_key[key], return_state=final[0])
            break
        if found is None:
            fallback.append(dict(site=i, pc=word, op=op, arg=arg))
        else:
            records.append(found)
    uses = collections.Counter(r['template'] for r in records)
    for t in templates:
        t['uses'] = uses[t['id']]
    return dict(allowed_return_states=sorted(allowed), templates_data=templates,
                guard_records=records, literal_controls=fallback)


def verify_existing_templates(table, path):
    data = read_json(path)['templates_data']
    steps = 0
    for t in data:
        start, end = immutable(t['start']), immutable(t['pre_home'])
        current = start
        for e in t['trace']:
            require(current == immutable(e['before']), 'Discontinuous received trace')
            require(not(current[1] and not current[2]), 'Received body reads its frame')
            result = step(table, current)
            require(result is not None and result[0] == immutable(e['after']) and result[1] == e['moved'],
                    'Received trace disagrees with independent maintained-step transcription')
            current = result[0]
            steps += 1
        require(current == end and t['steps'] == len(t['trace']), 'Bad received template endpoint')
    return dict(templates=len(data), symbolic_steps=steps)


def add_guard_fields(data, sites, ports, table):
    templates = data['templates_data']
    for rec in data['guard_records']:
        word, op, arg = sites[rec['site']]
        prefix, suffix = word[:rec['cut']], word[rec['cut']:]
        result, overflow = action(suffix, op, arg)
        streak = 0
        for b in reversed(prefix):
            streak = 0 if b == '1' else streak + 1
            require(streak < 8, 'scanBound0 premise unavailable')
        rec.update(prefix=prefix, suffix=suffix, result_suffix=result, op=op, argument=arg,
                   routed_state=ports[word], successor=action(word, op, arg)[0],
                   strip_count=suffix.count('1' if op == 'CC' else '0'),
                   stripped_suffix=strip(suffix, '1' if op == 'CC' else '0', arg),
                   carry_into_prefix=overflow,
                   result_length_le_suffix=len(result) <= len(suffix),
                   pc_length_bound_48=len(word) <= 48, local_gap_offset=48-len(word),
                   endpoint_gap_delta=len(suffix)-len(result), scanBound0_result=streak,
                   left_word_rows=word_scan_rows(table, rec['return_state'], prefix[::-1]+'1'))
        require(rec['return_state'] == templates[rec['template']]['return_state'], 'Wrong return state')
    return data


def validate_guard(rec, templates, sites, ports, table):
    word, op, arg = sites[rec['site']]
    template = templates[rec['template']]
    key = template['key']
    require(rec['pc'] == word and rec['op'] == op and rec['argument'] == arg, 'Wrong source site')
    prefix, suffix = word[:rec['cut']], word[rec['cut']:]
    require(prefix == rec['prefix'] and suffix == rec['suffix'], 'Incorrect prefix/suffix partition')
    require(ports[word] == key[1] == rec['routed_state'], 'Wrong routed state')
    require((suffix,op,arg)==tuple(key[2:5]), 'Template action mismatch')
    ok, result = source_frame_ok(suffix, op, arg)
    require(ok and result == key[6] == rec['result_suffix'], 'Source action crosses preserved prefix')
    require(action(word,op,arg)==(prefix+result,False), 'Whole source action mismatch')
    require(len(result) <= len(suffix) and len(word) <= 48, 'Gap side conditions fail')
    require(rec['local_gap_offset']==48-len(word) and rec['endpoint_gap_delta']==len(suffix)-len(result), 'Gap mismatch')
    require(rec['return_state']==template['return_state'], 'Wrong scanner state')
    require(word_scan_rows(table,rec['return_state'],prefix[::-1]+'1')==rec['left_word_rows'], 'Wrong scanner certificate')
    return True


def mutation_checks(data, sites, ports, table):
    templates=data['templates_data']
    first=data['guard_records'][0]
    mutations={
        'wrong_routed_state': ('routed_state', first['routed_state']+1),
        'wrong_gap_offset': ('local_gap_offset', first['local_gap_offset']+1),
        'wrong_gap_delta': ('endpoint_gap_delta', first['endpoint_gap_delta']+1),
        'wrong_result_suffix': ('result_suffix', first['result_suffix']+'1'),
        'wrong_return_state': ('return_state', 999),
        'wrong_source_word': ('pc', first['pc']+'1'),
    }
    rejected=[]
    for name,(field,value) in mutations.items():
        candidate=copy.deepcopy(first);candidate[field]=value
        try:
            validate_guard(candidate,templates,sites,ports,table)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError('Mutation unexpectedly accepted: '+name)
    # Algebraic frame counterexample: an empty-left step invents blank; a real
    # appended true frame instead gets read. This requires the guarded theorem.
    empty=(2,True,(),(('b',1),))
    framed=(2,True,(('b',1),),(('b',1),))
    a=step(table,empty)[0];b=step(table,framed)[0]
    lifted=(a[0],a[1],a[2]+(('b',1),),a[3])
    require(lifted!=b, 'Missing empty-left counterexample')
    # Dropping an explicit left trailing zero becomes false after a one frame.
    require((('b',0),('b',1))!=(('b',1),), 'Missing normL frame counterexample')
    # Literal source-action counterexamples to missing count/carry guards.
    require(strip('1'+'0','1',1)!='1'+strip('0','1',1), 'Missing strip counterexample')
    require(increment('0'+'1')[0]!='0'+increment('1')[0], 'Missing carry counterexample')
    return dict(rejected_mutations=rejected, unsafe_empty_left_rejected=True,
                dropping_left_zero_before_frame_rejected=True,
                crossing_strip_rejected=True, prefix_carry_rejected=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    z = args.repo / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
    r = args.repo / 'Computability/BusyBeaver/Research/ZFC'
    paths = dict(table=z/'KTable215.lean', decoder=z/'K215Decoder.lean', runtime=z/'KRuntimeCore.lean',
                 home=z/'KHome.lean', sites=r/'candidate-k215/sites215.json',
                 native=r/'candidate-k215/k215.native.tm', dense=r/'candidate-k215/k215.tm',
                 received=r/'k225-formal/verification/k215/simplification/proposals/round13-left-frame/runtime/FORMAL_TEMPLATES.json')
    table = parse_table(paths['table'].read_text())
    rename=lambda q:{301:102,302:120,254:230}.get(q,q)
    native={}
    for line in paths['native'].read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t=line.split()
        native[rename(int(q)),int(b)]=(int(w),d=='R',rename(int(t)))
    require(native==table,'Current native/formal tables differ under documented relabeling')
    nodes, roles, root = parse_decoder(paths['decoder'].read_text())
    sites = read_json(paths['sites'])
    ports = bind_sites(nodes, roles, root, table, sites)
    old = verify_existing_templates(table, paths['received'])
    q2 = discover(table, sites, ports, {2})
    improved = add_guard_fields(discover(table, sites, ports, {1, 2}),sites,ports,table)
    broader=discover(table,sites,ports,{1,2,3,5,9,15,23,34,50})
    require([(t['key'],t['start'],t['pre_home'])for t in broader['templates_data']]==
            [(t['key'],t['start'],t['pre_home'])for t in improved['templates_data']],
            'Broader return scanner discovered a distinct factorization')
    for record in improved['guard_records']:
        validate_guard(record,improved['templates_data'],sites,ports,table)
    negative=mutation_checks(improved,sites,ports,table)
    require(len(q2['templates_data']) == 35 and len(q2['guard_records']) == 1422,
            'Independent baseline extraction did not reproduce round13 counts')
    args.out.mkdir(parents=True, exist_ok=True)
    for name, value in [('templates-q2.json', q2), ('templates-q1q2.json', improved)]:
        (args.out/name).write_text(json.dumps(value, separators=(',', ':'))+'\n')
    summary = dict(status='PASS_FINITE_INDEPENDENT_AUDIT', source_sites=len(sites), machine_actions=len(table),
                   exact_source_tree_reexpansion=True, exact_routed_ports=len(ports), received_replay=old,
                   native_formal_table_equality=True,
                   original=dict(templates=len(q2['templates_data']), uses=len(q2['guard_records']),
                                 local_steps=sum(t['steps'] for t in q2['templates_data'])),
                   proposed=dict(templates=len(improved['templates_data']), uses=len(improved['guard_records']),
                                 local_steps=sum(t['steps'] for t in improved['templates_data']),
                                 literal_controls=improved['literal_controls'],
                                 return_states=dict(collections.Counter(t['return_state'] for t in improved['templates_data'])),
                                 control_guard_return_states=dict(collections.Counter(t['return_state'] for t in improved['guard_records'])),
                                 broader_scanner_set_produces_same_templates=True,
                                 expensive_obligations=1900+2850+1+len(improved['templates_data'])+len(improved['literal_controls'])),
                   mutation_checks=negative,
                   input_pins={k:dict(path=str(p.relative_to(args.repo)), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
                               for k,p in paths.items()},
                   scope='Finite transcription, source/route attachment and affine endpoint audit only. No theorem or endpoint compilation.')
    (args.out/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='input_pins'}, indent=2))


if __name__ == '__main__':
    main()
