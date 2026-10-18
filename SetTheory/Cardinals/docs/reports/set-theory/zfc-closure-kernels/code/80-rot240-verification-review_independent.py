#!/usr/bin/env python3
"""Independent small review of the source rotation and the four tape blocks.

Does not import any candidate-producer or runtime-checker module.  Inputs are
read as literal data.  Source proof is the indicated induction on R6, not a
finite execution bound.  This is executable ordinary mathematics, not Lean.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Run with assertions enabled; Python -O is not accepted.')

HERE = Path(__file__).resolve().parent
EXPECTED = {
    'reference/baseline_sites.json': '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4',
    'machines/sites_logical.json': '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d',
    'reference/baseline241_old.tm': '1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3',
    'reference/rotated241_old.tm': '88a1f42b01b7e2b4bf29bc1b3819b78f1e7a17cefaefbc003654f2f5cc202c2f',
    'machines/zfc240_old.tm': '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f',
}


def digest(p):
    return sha256(p.read_bytes()).hexdigest()


def table(path):
    out = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        assert (q, b) not in out and b in (0, 1) and w in (0, 1)
        assert d in ('L', 'R')
        out[q, b] = w, (-1 if d == 'L' else 1), z
    return out


class Source:
    """Recursive ancestor-stack semantics, independent of producer helpers."""
    def __init__(self, path):
        rows = json.loads(path.read_text())
        self.leaves = {tuple(map(int, p)): (op, r) for p, op, r in rows}
        assert len(self.leaves) == len(rows)
        prefixes = {p[:k] for p in self.leaves for k in range(len(p))}
        assert not prefixes.intersection(self.leaves)
        assert len(prefixes) + 1 == len(self.leaves)
        for p in prefixes:
            for b in (0, 1):
                assert p + (b,) in self.leaves or p + (b,) in prefixes

    def first(self, address):
        while address not in self.leaves:
            address += (0,)
        return address

    @staticmethod
    def next_subtree(address):
        if not address:
            return ()
        if address[-1] == 0:
            return address[:-1] + (1,)
        return Source.next_subtree(address[:-1])

    @staticmethod
    def leave_frames(address, direction, count):
        if count == 0 or not address:
            return address
        return Source.leave_frames(address[:-1], direction,
                                   count - (address[-1] == direction))

    def target(self, leaf, positive=False):
        op, register = self.leaves[leaf]
        if op == 'CH':
            return None
        if op == 'CI' or (op == 'CD' and positive):
            address = self.next_subtree(leaf)
        elif op in ('CD', 'CB'):
            count = 1 if op == 'CD' else register
            address = self.next_subtree(self.leave_frames(leaf, 0, count))
        elif op == 'CC':
            address = self.leave_frames(leaf, 1, register)
        else:
            raise ValueError(op)
        return self.first(address)


def word(address):
    return None if address is None else ''.join(map(str, address))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=HERE.parent,
                        help='Package root containing reference/ and machines/')
    parser.add_argument('--output', type=Path,
                        help='Defaults to PACKAGE/evidence/review_independent.json')
    args = parser.parse_args()
    root = args.root
    bindings = []
    for name, expected in EXPECTED.items():
        actual = digest(root / name)
        assert actual == expected, ('Unexpected input bytes', name, expected, actual)
        bindings.append({'path': name, 'expected_sha256': expected,
                         'actual_sha256': actual, 'matches': True})
    old = Source(root / 'reference/baseline_sites.json')
    new = Source(root / 'machines/sites_logical.json')
    root_words = ['11101001001011000011', '1110100100101110011',
                  '1110100101100011', '111110011']
    roots = [tuple(map(int, p)) for p in root_words]
    assert all(not (r[:len(s)] == s) for r in roots for s in roots if r != s)
    old_local = {r + s for r in roots for s in [(0,0), (0,1,0), (0,1,1), (1,)]}
    new_local = {r + s for r in roots for s in [(0,), (1,0), (1,1)]}
    border = {old.first(r): new.first(r) for r in roots}
    outside = set(old.leaves) - old_local
    assert outside == set(new.leaves) - new_local
    assert old.first(()) == new.first(())
    ingress = {r: [] for r in roots}
    count = 0
    for p in outside:
        assert old.leaves[p] == new.leaves[p]
        for positive in ([False, True] if old.leaves[p][0] == 'CD' else [False]):
            a, b = old.target(p, positive), new.target(p, positive)
            assert border.get(a, a) == b
            if a in old_local:
                assert a in border
                r = next(r for r in roots if old.first(r) == a)
                ingress[r].append([word(p), positive])
            if b in new_local:
                assert b in border.values()
            count += 1
    macros = []
    for r in roots:
        a, b, c, d = [r + s for s in [(0,0), (0,1,0), (0,1,1), (1,)]]
        e, f, g = [r + s for s in [(0,), (1,0), (1,1)]]
        assert [old.leaves[p] for p in (a,b,c,d)] == [('CD',6), ('CI',5), ('CC',2), ('CI',5)]
        assert [new.leaves[p] for p in (e,f,g)] == [('CI',5), ('CD',6), ('CC',2)]
        assert old.target(a, False) == d
        assert old.target(a, True) == b and old.target(b) == c and old.target(c) == a
        assert new.target(e) == f and new.target(f, True) == g and new.target(g) == e
        assert old.target(d) == new.target(f, False)
        assert old.target(d) not in old_local | new_local
        assert len(ingress[r]) == 1
        macros.append({'root': word(r), 'entry_old': word(a), 'entry_new': word(e),
                       'exit': word(old.target(d)), 'outside_ingress': ingress[r]})
    assert count == 8370

    prior = table(root / 'reference/baseline241_old.tm')
    rotated = table(root / 'reference/rotated241_old.tm')
    final = table(root / 'machines/zfc240_old.tm')
    assert set(prior) == set(rotated)
    assert {k: v for k,v in rotated.items() if prior[k] != v} == {
        (142,0):(0,1,72), (142,1):(1,1,17)}
    assert set(rotated) - set(final) == {(90,0), (90,1)}
    assert not (set(final) - set(rotated))
    assert {k: v for k,v in final.items() if rotated[k] != v} == {
        (72,0):(0,-1,144), (72,1):(1,-1,36), (79,1):(1,1,72)}
    mapping = lambda q: 72 if q == 90 else q
    states = {q for q,b in final}
    assert len(final) == 480 and len(states) == 240
    assert {z for w,d,z in final.values()} - states == {254}
    assert set(final) == {(q,b) for q in states for b in (0,1)}
    incoming = {target: sorted((q,b,w,d) for (q,b),(w,d,z) in rotated.items()
                               if z == target) for target in (55,142,72,90)}
    assert incoming == {
        55:[(37,1,1,1)], 142:[(119,1,1,1)],
        72:[(55,0,0,1),(142,0,0,1)], 90:[(79,1,1,1)]}
    assert 95 not in incoming
    for (q,b),(w,d,z) in rotated.items():
        if q not in (72,90):
            assert final[mapping(q),b] == (w,d,mapping(z))

    # For the exceptional blocks every read value is known symbolically.
    # The exterior is arbitrary and is never represented, read, or written.
    blocks = []
    for old_state, bit, length in [(72,0,9), (72,1,3), (90,0,3), (90,1,3)]:
        cells = {-1: 0 if old_state == 72 else 1, 0: bit}
        if old_state == 72:
            cells[-2] = 1
        expected = cells.copy()
        w,d,z = rotated[old_state,bit]
        expected[0] = w
        q,h = mapping(old_state),0
        path = []
        for _ in range(length):
            assert q != 254 and h in cells
            b = cells[h]
            path.append([q,h,b])
            nw,nd,nq = final[q,b]
            cells[h] = nw
            q,h = nq,h+nd
        assert (q,h,cells) == (mapping(z),d,expected)
        blocks.append({'old_state':old_state, 'read':bit, 'steps':length,
                       'candidate_path':path, 'exit_state':q,
                       'exit_head':h, 'matches_old_step_on_every_inspected_cell':True})

    report = {
        'status':'INDEPENDENT_SOURCE_AND_LOCAL_REVIEW_PASS',
        'checker_sha256': digest(Path(__file__)),
        'input_bindings': bindings,
        'outside_guarded_edges':count, 'macros':macros,
        'source_induction':{
            'variables':'R5=m,R6=n, arbitrary naturals; all other registers arbitrary',
            'n_zero':'Both execute CI5 once and one failed CD6, exit with (m+1,0) in 2 source instructions',
            'n_positive':'One CI5, one successful CD6, one CC2 return to the corresponding entry with (m+1,n-1)',
            'conclusion':'Finite exit at identical outside instruction with R5=m+n+1,R6=0, other registers unchanged, in 3n+2 source instructions',
            'CC2_scope':'Old p011 removes final two ones to p0, first leaf p00. New p11 removes final two ones to p, first leaf p0. Neither pops outside the replacement root.',
        },
        'exceptional_blocks':blocks,
        'incoming_rows':incoming,
        'inductive_guard_argument':{
            '55':'Only incoming row is37/1=1R55, hence immediate left cell1',
            '142':'Only incoming row is119/1=1R142, hence immediate left cell1',
            '72':'Only incoming rows55/0 and142/0 write0 and move right; predecessor invariant gives left pair10',
            '90':'Only incoming row79/1=1R90, hence immediate left cell1',
            'initial':'Start95 is unconstrained, so these state-conditional guards hold on every input tape',
        },
        'review_scope':'Independent data parser, source ancestor semantics and symbolic finite-tape block replay; does not duplicate the full8386-case parameterized runtime proof or upstream SIR/ZFC proof. Ordinary proof formalizable in ZFC; no proof-assistant endpoint claimed.',
        'required_bridge':'Use full rotated-table runtime theorem for rotated142_sites, exact rotated blank initialization, source induction above, and inherited baseline241 calibration; then apply local all-tape fold.',
    }
    output = args.output or root / 'evidence/review_independent.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
