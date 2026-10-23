#!/usr/bin/env python3
"""Independent, fail-closed finite-data review. Never executes upstream code.

This checks saved source text, not Lean/Rocq elaboration or kernel correctness.
It deliberately does not import either proposal's audit implementation.
"""
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def clean(text):
    # Lean nested comments and line comments; enough for these literal modules.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, 'unclosed comment')
    return ''.join(out)


def declaration(text, name):
    s = clean(text)
    match = re.search(r'^def ' + re.escape(name) + r'\b([^\n]*)(.*?)(?=\n(?:def |theorem |end )|\Z)', s, re.M | re.S)
    require(match is not None, 'missing declaration ' + name)
    header = match.group(1)
    return (header.split(':=', 1)[1] if ':=' in header else '') + match.group(2)


def edge_pair(rhs):
    """Fully parse pairs, parentheses, and every Edge constructor used here."""
    tokens = re.findall(r'\.[A-Za-z]+|[0-9]+|some|none|[(),]|\S', rhs)
    pos = 0

    def expr():
        nonlocal pos
        require(pos < len(tokens), 'truncated expression')
        token = tokens[pos]
        pos += 1
        if token == 'some':
            return expr()
        if token == 'none':
            return None
        if token == '(':
            a = expr()
            require(pos < len(tokens), 'unclosed expression')
            if tokens[pos] == ',':
                pos += 1
                a = (a, expr())
            require(tokens[pos] == ')', 'expected closing parenthesis')
            pos += 1
            return a
        require(token in ('.node', '.inc', '.decnz', '.brk', '.cont', '.halt'), 'unknown edge ' + token)
        if token == '.halt':
            return ('halt', 0)
        require(pos < len(tokens) and tokens[pos].isdigit(), 'missing edge argument')
        n = int(tokens[pos])
        pos += 1
        return (token[1:], n)

    result = expr()
    require(pos == len(tokens), 'unconsumed expression: ' + rhs)
    return result


def table(text, name):
    out, default_seen = {}, False
    for line in declaration(text, name).splitlines():
        if not line.strip():
            continue
        m = re.fullmatch(r'\s*\|\s*(\d+|_)\s*=>\s*(.*?)\s*', line)
        require(m is not None, 'unrecognized literal row: ' + line)
        value = edge_pair(m[2])
        if m[1] == '_':
            require(not default_seen, 'duplicate default')
            default_seen = True
        else:
            n = int(m[1])
            require(not default_seen and n not in out, 'duplicate or shadowed row')
            out[n] = value
    require(default_seen, 'missing default')
    return out


def parse_bits(s):
    xs = [x.strip() for x in s.split(',')] if s.strip() else []
    require(all(x in ('false', 'true') for x in xs), 'bad bit')
    return tuple(x == 'true' for x in xs)


def array(text, name):
    s = clean(text)
    m = re.search(r'^def ' + name + r' : Array \w+ := #\[\n(.*?)\n\]', s, re.M | re.S)
    require(m is not None, 'missing array ' + name)
    return [x.strip().rstrip(',') for x in m[1].splitlines() if x.strip()]


def infer(table_, reverse, fuel=156, start=236):
    n, word = start, []
    for _ in range(fuel + 1):
        if n == 457:
            return word
        if len(word) == fuel:
            return None
        row = table_.get(n)
        if row is None or row[0][0] != 'node' or row[1][0] != 'node':
            return None
        a = reverse.get(row[0][1])
        if a is None:
            return None
        word.append(a)
        n = row[1][1]
    return None


def ax_review():
    base = ROOT / 'root'
    source = {p.name: p.read_text() for p in (base / 'sources').glob('*.lean')}
    receipt = json.loads((base / 'AX_INFERENCE_AUDIT.json').read_text())
    require(receipt['pin'] == PIN, 'pin')
    for name, digest in receipt['source_sha256'].items():
        require(hashlib.sha256((base / 'sources' / name).read_bytes()).hexdigest() == digest, 'AX source digest ' + name)
    tables = [table(source[f], d) for f, d in [('Dag222.lean', 'dagNodes'), ('Dag219.lean', 'eqNodes'), ('DagDom.lean', 'axNodes'), ('DagPerm.lean', 'permNodes')]]
    require([len(t) for t in tables] == [461, 7, 18, 7], 'AX row counts')
    require('(eqNodes n).getD (Dag222.dagNodes n)' in source['Dag219.lean'], '219 overlay precedence')
    require('(axNodes n).getD (Dag219.dagNodes n)' in source['DagDom.lean'], 'Dom overlay precedence')
    require('(permNodes n).getD (DagDom.dagNodes n)' in source['DagPerm.lean'], 'Perm overlay precedence')
    graphs = {'Dom': tables[0] | tables[1] | tables[2], 'Perm': tables[0] | tables[1] | tables[2] | tables[3]}
    result, old_total, new_total = {}, 0, 0
    words = {}
    for lane, graph in graphs.items():
        name = 'L2Axioms' + lane + '.lean'
        old = source[name]
        new = (base / 'drafts' / name).read_text()
        atoms_text = declaration(old, 'AXAtom.node')
        pairs = re.findall(r'\|\s*\.([a-z0-9]+)\s*=>\s*(\d+)', atoms_text)
        remainder = re.sub(r'\|\s*\.([a-z0-9]+)\s*=>\s*(\d+)', '', atoms_text)
        require(not remainder.strip(), 'unparsed atom map')
        atoms = {a: int(n) for a, n in pairs}
        require(len(atoms) == len(pairs) == len(set(atoms.values())) == 13, 'atom map injectivity')
        literal = re.search(r'def axWord : List AXAtom := \[(.*?)\]', old, re.S)
        require(literal is not None, 'literal word')
        names = re.findall(r'\.([a-z0-9]+)', literal[1])
        require(not re.sub(r'\.[a-z0-9]+|\s|,', '', literal[1]), 'unparsed word')
        reverse = {v: k for k, v in atoms.items()}
        require(infer(graph, reverse) == names and len(names) == 156, 'extracted word mismatch')
        words[lane] = names
        replacement = f'def axWord : List AXAtom :=\n  (MacroWordInference.inferWord dag{lane}.nodes AXAtom.decode 457 156 236).getD []'
        decode = 'def AXAtom.decode (n : Nat) : Option AXAtom :=\n  ([' + ', '.join('.' + a for a in atoms) + '] : List AXAtom).find?\n    (fun a => a.node == n)\n\n'
        expected = 'import BusyBeaver.ZFC.MacroWordInference\n' + old[:literal.start()] + replacement + old[literal.end():]
        expected = expected.replace('theorem AXAtom.run', decode + 'theorem AXAtom.run', 1)
        require(expected == new, 'unexpected draft edit')
        for anchor in ('def axWordCheck', 'theorem axWordRun', 'theorem axWord_checked'):
            if anchor == 'theorem axWord_checked':
                require(old[old.index(anchor):] == new[new.index(anchor):], 'changed downstream proof text')
        require(infer(graph, reverse, 155) is None, 'fuel control')
        bad = dict(graph); bad[236] = (('halt', 0), ('node', 457))
        require(infer(bad, reverse) is None, 'non-node overlay control')
        bad = dict(graph); bad[236] = (('node', 166), ('node', 236))
        require(infer(bad, reverse) is None, 'cycle/fuel control')
        bad = dict(graph); bad[236] = (('node', 999), ('node', 457))
        require(infer(bad, reverse) is None, 'unknown macro control')
        old_total += len(old.encode()); new_total += len(new.encode())
        result[lane] = {'atoms': len(names), 'decoder_atom_kinds': len(atoms), 'all_nonproposal_text_identical': True, 'word': names}
    helper_bytes = (base / 'drafts' / 'MacroWordInference.lean').stat().st_size
    require(old_total - new_total - helper_bytes == 787, 'net byte delta')
    # Parser controls: comments are ignored; malformed/duplicate cases fail closed.
    sample = 'def sample : Nat → Edge × Edge :=\n | 0 => (.node 1, .node 2)\n | _ => (.halt, .halt)\n'
    require(table('/- | 0 => (.node 99, .node 98) -/\n' + sample, 'sample')[0] == (('node', 1), ('node', 2)), 'comment parsing')
    for corrupt in (sample.replace('.node 2)', '.unknown 2)'), sample.replace(' | _', ' | 0 => (.node 1, .node 2)\n | _')):
        try:
            table(corrupt, 'sample')
        except ValueError:
            pass
        else:
            raise ValueError('parser accepted mutation')
    old_lines = sum(len(source['L2Axioms'+lane+'.lean'].splitlines()) for lane in graphs)
    new_lines = sum(len((base/'drafts'/('L2Axioms'+lane+'.lean')).read_text().splitlines()) for lane in graphs) + len((base/'drafts'/'MacroWordInference.lean').read_text().splitlines())
    return {'lanes': result, 'differing_word_positions_one_based': [i+1 for i, (a, b) in enumerate(zip(words['Dom'], words['Perm'])) if a != b], 'source_bytes': old_total, 'overlay_bytes': new_total, 'helper_bytes': helper_bytes, 'net_bytes_saved': old_total-new_total-helper_bytes, 'old_lines': old_lines, 'new_lines_with_helper': new_lines, 'negative_controls': ['fuel', 'non-node overlay', 'cycle', 'unknown macro', 'comment injection', 'unknown constructor', 'duplicate row']}


def decoder_review():
    base = ROOT / 'decoder'
    provenance = json.loads((base / 'source_provenance.json').read_text())
    require(provenance['pin'] == PIN, 'decoder pin')
    for item in provenance['sources']:
        data = (base / 'sources' / item['name']).read_bytes()
        digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(digest == item['github_blob_sha'], 'decoder input changed')
    s = (base / 'sources' / 'K215Decoder.lean').read_text()
    ps = (base / 'sources' / 'KSource215Program.lean').read_text()
    require(re.search(r'^def sourceRoot : Nat := 201$', clean(s), re.M), 'source root metadata')
    require(re.search(r'^def p215 : Program := ⟨p215Nodes, 178, 179⟩$', clean(ps), re.M), 'program metadata')
    nodes = []
    for line in array(s, 'sourceNodes'):
        m = re.fullmatch(r'\.(leaf|fork) (\d+) (\d+)', line)
        require(m is not None, 'bad source node')
        nodes.append((m[1], int(m[2]), int(m[3])))
    pnodes = table(ps, 'p215Nodes')
    forks = [i for i, (tag, _, _) in enumerate(nodes) if tag == 'fork']
    labels = dict(zip(forks, range(len(forks))))
    ops = ('inc', 'decnz', 'brk', 'cont', 'halt')
    def image(i):
        tag, a, b = nodes[i]
        return ('node', labels[i]) if tag == 'fork' else (ops[a], b)
    require(len(nodes) == 202 and len(labels) == len(pnodes) == 179, 'decoder sizes')
    require(labels[201] == 178, 'decoder roots')
    for i in forks:
        _, l, r = nodes[i]
        require(l < i and r < i, 'nondecreasing source edge')
        require(pnodes[labels[i]] == (image(l), image(r)), 'noncommuting source square')
    blocks = []
    for line in array(s, 'blocks'):
        m = re.fullmatch(r'⟨(\d+), (\d+), \[([^\]]*)\], (\d+)⟩', line)
        require(m is not None, 'bad block')
        blocks.append((int(m[1]), int(m[2]), parse_bits(m[3]), int(m[4])))
    roles = []
    edge_re = r'(?:\(\.internal \d+ \d+\)|\(\.primitive \d+ ⟨(?:false|true), (?:1|\(-1\)), \d+⟩\))'
    for line in array(s, 'roles'):
        m = re.fullmatch(r'⟨(\d+), (\d+), \[([^\]]*)\], ('+edge_re+'), ('+edge_re+')⟩', line)
        require(m is not None, 'bad role')
        edges = []
        for e in (m[4], m[5]):
            nums = [int(n) for n in re.findall(r'-?\d+', e)]
            edges.append(('internal', *nums) if e.startswith('(.internal') else ('primitive', nums[0]))
        roles.append((int(m[1]), int(m[2]), parse_bits(m[3]), *edges))
    pilot = (base / 'DirectProgramCertificateDraft.lean').read_text()
    expected_role_lines = []
    for line in array(s, 'roles'):
        line = re.sub(r'^⟨(\d+)', lambda m: '⟨'+str(labels[int(m[1])]), line)
        line = re.sub(r'\.primitive \d+ ', '.primitive ', line)
        expected_role_lines.append(line)
    require(array(pilot, 'roles') == expected_role_lines, 'pilot changed more than labels/primitive IDs')
    require('| .primitive action, _ => decide (M r.state bit = some action)' in pilot, 'reviewed terminal checker branch changed')
    counts = Counter()
    for n, q, suffix, *edges in roles:
        require(n in labels and 0 < len(suffix) <= 2, 'bad role source')
        for bit, e in enumerate(edges):
            counts[e[0]] += 1
            child = nodes[n][bit+1]
            require(pnodes[labels[n]][bit] == image(child), 'retargeted edge')
            if e[0] == 'internal':
                _, k, j = e
                target, tq, ts, *_ = roles[k]
                entry, exit_, word, steps = blocks[j]
                full = suffix + (bool(bit),)
                require(target == child and ts == full[-2:] and q == entry and tq == exit_, 'internal block routing')
                require(0 < len(word) <= len(full) and word == full[-len(word):] and 1 <= steps <= 7, 'internal word')
            else:
                require(e[1] == child and nodes[child][0] == 'leaf', 'primitive identity')
    leaves = []
    def expand(i, prefix=()):
        tag, a, b = nodes[i]
        if tag == 'leaf':
            leaves.append((prefix, image(i)))
        else:
            expand(a, prefix+(False,)); expand(b, prefix+(True,))
    expand(201)
    def walk(bits):
        n = 178
        for depth in range(180):
            e = pnodes[n][int(bits[depth]) if depth < len(bits) else 0]
            if e[0] != 'node':
                return e, depth+1
            n = e[1]
        return None
    for bits, e in leaves:
        require(walk(bits) == (e, len(bits)), 'leaf walk')
        trimmed = list(bits)
        while trimmed and not trimmed[-1]:
            trimmed.pop()
        require(walk(trimmed) == (e, len(bits)), 'zero padding')
        for tail in ((True,), (False,), (True, False, True)):
            require(walk(bits+tail) == (e, len(bits)), 'unread suffix')
    require(len(roles) == 234 and len(blocks) == 281 and len(leaves) == 4751, 'decoder counts')
    return {'source_nodes': len(nodes), 'mapped_forks': len(labels), 'roles': len(roles), 'blocks': len(blocks), 'branches': dict(counts), 'expanded_leaves': len(leaves), 'guarded_outcome_count_only': sum(1+(e[0]=='decnz') for _, e in leaves), 'pilot_only_retargets_labels_and_removes_primitive_ids': True, 'terminal_check_invariant_under_primitive_opcode_change': True, 'checked': 'literal source mapping and routing metadata; not physical actions, block execution, or universal semantics'}


def rocq_review():
    base = ROOT / 'rocq'
    p = (base / 'sources' / 'ProgLibPerm.v').read_text()
    draft = (base / 'z465_replacement.v').read_text()
    old = re.search(r'Lemma z465 a :.*?Qed\.', p, re.S)[0]
    new = re.search(r'Lemma z465_reuse a :.*?Qed\.', draft, re.S)[0].replace('z465_reuse', 'z465').replace('a : forall m, get m 5 = a ->\n  sem', 'a : forall m, get m 5 = a -> sem')
    require(old.split('Proof.')[0] == new.split('Proof.')[0], 'z465 statement')
    dag = (base / 'sources' / 'DagPerm.v').read_text()
    row = lambda n: re.search(r'^\s*\| '+str(n)+r' => (.*)$', dag, re.M)[1]
    require(row(199) == row(465) == '(EDecnz 5, EContinue 1)', 'loop row')
    require(len(old.encode()) == 475 and len(new.encode()) == 171, 'z465 byte count')
    return {'old_declaration_bytes': len(old.encode()), 'new_declaration_bytes': len(new.encode()), 'old_declaration_lines': len(old.splitlines()), 'new_declaration_lines': len(new.splitlines()), 'same_statement': True, 'same_loop_row_as_199': True, 'compiled': False}


if __name__ == '__main__':
    result = {'pin': PIN, 'status': 'PASS: independent static data checks only', 'ax': ax_review(), 'decoder': decoder_review(), 'rocq': rocq_review(), 'formal_compilation_performed': False, 'upstream_code_executed': False}
    (Path(__file__).parent / 'INDEPENDENT_DATA_CHECK.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'ax'}, indent=2))
    print('AX: two 156-atom words match; all unproposed text identical; net 787 bytes saved.')
