"""Total finite binary-word codec and fair search for fixed C254 circuits.

The trusted caller fixes the exact circuit tables. A candidate cannot choose
rules, circuit lengths or the falsity target. No resource exception becomes
'rejected' or 'consistent'; no actual binary Turing machine is supplied.
"""
from itertools import product

import term_circuits as V


class Malformed(ValueError):
    pass


def require(test, reason):
    if not test:
        raise Malformed(reason)


class Reader:
    def __init__(self, bits):
        self.bits = bits
        self.pos = 0

    @property
    def remaining(self):
        return len(self.bits) - self.pos

    def bit(self):
        require(self.pos < len(self.bits), 'truncated')
        out = ord(self.bits[self.pos]) - ord('0')
        self.pos += 1
        return out

    def fixed(self, width):
        out = 0
        for _ in range(width):
            out = 2*out + self.bit()
        return out

    def natural(self):
        out = 0
        while self.bit():
            out += 1
        return out

    def path(self):
        out = []
        while self.bit():
            out.append(self.bit())
        return out


def decode(bits, templates, *, stats=None):
    """Return a structurally valid finite certificate or None, for every word.

    Unary n is1^n0. A path uses end0/left10/right11. Arena/proof counts
    are bounded by actual remaining bits before any per-record allocation.
    Logical validity, gate truth and fixedF are checked by V, not by decoding.
    """
    if stats is None:
        stats = {}
    stats.update(bits=len(bits) if type(bits) is str else None, consumed=0,
                 positive_nodes=0, proof_rows=0, reason=None)
    try:
        require(type(bits) is str and all(b in '01' for b in bits), 'not_binary_word')
        r = Reader(bits)
        count = r.natural()
        # Every positive node needs2 tag bits +2 terminating unary zero bits.
        require(count <= r.remaining//4, 'node_count_exceeds_remaining_bits')
        nodes = [['z']]
        for i in range(1, count + 1):
            tag, left, right = r.fixed(2), r.natural(), r.natural()
            require(left < i and right < i, 'node_forward_reference')
            require((tag, left, right) != (0, 0, 0), 'zero_alias')
            nodes.append(['b', tag, left, right])
        stats['positive_nodes'] = count
        rows_count = r.natural()
        # Every row needs4 tag bits +one terminating formula-ID zero bit.
        require(rows_count <= r.remaining//5, 'row_count_exceeds_remaining_bits')
        rows = []
        for i in range(rows_count):
            tag = r.fixed(4)
            require(tag < 12, 'unknown_rule')
            args = []
            for _ in range(V.ARITY[tag]):
                value = r.natural()
                require(value < len(nodes), 'argument_reference')
                args.append(value)
            children = []
            for _ in range(2 if tag == 1 else 1 if tag == 2 else 0):
                value = r.natural()
                require(value < i, 'proof_forward_reference')
                children.append(value)
            formula = r.natural()
            require(formula < len(nodes), 'formula_reference')
            row = {'tag': tag, 'args': args, 'children': children, 'formula': formula}
            if tag >= 3:
                ids = []
                for _ in templates[tag].steps:
                    value = r.natural()
                    require(value < len(nodes), 'circuit_reference')
                    ids.append(value)
                row['constructor_ids'] = ids
            if tag == 11:
                row['gate_paths'] = [r.path(), r.path()]
            rows.append(row)
        stats['proof_rows'] = rows_count
        require(r.remaining == 0, 'leftover_bits')
        stats['consumed'] = r.pos
        return {'format': V.FORMAT, 'nodes': nodes, 'proof_rows': rows}
    except Malformed as error:
        stats['reason'] = str(error)
        return None


def encode(cert, templates):
    """Produce a word for the canonical structural interface; no verifier call.

    Extra certificate fields are rejected, rather than silently discarded.
    Semantic rule/gate validity is deliberately not required for roundtrip.
    """
    require(type(cert) is dict and set(cert) == {'format', 'nodes', 'proof_rows'}
            and cert['format'] == V.FORMAT, 'certificate_fields')
    nodes = cert['nodes']
    require(type(nodes) is list and nodes and nodes[0] == ['z'], 'zero_node')
    pieces = []
    def nat(n):
        pieces.append('1'*n + '0')
    def fixed(n, width):
        pieces.append(format(n, '0'+str(width)+'b'))
    def index(n, bound, reason):
        require(type(n) is int and 0 <= n < bound, reason)
        nat(n)
    nat(len(nodes)-1)
    for i, node in enumerate(nodes[1:], 1):
        require(type(node) is list and len(node) == 4 and node[0] == 'b', 'node_shape')
        _, tag, left, right = node
        require(type(tag) is int and 0 <= tag < 4, 'node_tag')
        require((tag, left, right) != (0, 0, 0), 'zero_alias')
        fixed(tag, 2)
        index(left, i, 'node_forward_reference')
        index(right, i, 'node_forward_reference')
    rows = cert['proof_rows']
    require(type(rows) is list, 'proof_list')
    nat(len(rows))
    for i, row in enumerate(rows):
        require(type(row) is dict, 'row_shape')
        tag = row['tag']
        require(type(tag) is int and 0 <= tag < 12, 'proof_tag')
        fields = {'tag', 'args', 'children', 'formula'}
        if tag >= 3:
            fields.add('constructor_ids')
        if tag == 11:
            fields.add('gate_paths')
        require(set(row) == fields, 'row_fields')
        fixed(tag, 4)
        args, children = row['args'], row['children']
        require(type(args) is list and len(args) == V.ARITY[tag], 'argument_arity')
        for a in args:
            index(a, len(nodes), 'argument_reference')
        require(type(children) is list and len(children) ==
                (2 if tag == 1 else 1 if tag == 2 else 0), 'premise_arity')
        for child in children:
            index(child, i, 'proof_forward_reference')
        index(row['formula'], len(nodes), 'formula_reference')
        if tag >= 3:
            ids = row['constructor_ids']
            require(type(ids) is list and len(ids) == len(templates[tag].steps), 'circuit_arity')
            for root in ids:
                index(root, len(nodes), 'circuit_reference')
        if tag == 11:
            paths = row['gate_paths']
            require(type(paths) is list and len(paths) == 2, 'gate_arity')
            for path in paths:
                require(type(path) is list and all(type(b) is int and b in (0, 1) for b in path),
                        'gate_path')
                for b in path:
                    pieces.append('1'+str(b))
                pieces.append('0')
    return ''.join(pieces)


def accepts(bits, templates):
    """The fixed-refutation predicate; there is no caller-selected goal here."""
    cert = decode(bits, templates)
    return cert is not None and V.verify_certificate(cert, templates)


def words_at_length(length):
    """All length-exact words in lexicographic order, including the empty word."""
    require(type(length) is int and length >= 0, 'length')
    for bits in product('01', repeat=length):
        yield ''.join(bits)


def words():
    """Fair length-lex enumeration of all finite binary words, once each."""
    length = 0
    while True:
        yield from words_at_length(length)
        length += 1


def semidecide(templates):
    """Return the first accepted fixedF word, or continue forever.

    This is an executable mathematical specification, not a Turing machine.
    No exception or exhausted finite level is interpreted as consistency.
    """
    for bits in words():
        if accepts(bits, templates):
            return bits


def search_through(max_length, templates):
    """Optional bounded diagnostic, expressly different from semidecide."""
    require(type(max_length) is int and max_length >= 0, 'length')
    tested = 0
    for length in range(max_length+1):
        for bits in words_at_length(length):
            tested += 1
            if accepts(bits, templates):
                return {'status': 'accepted_fixedF', 'tested_words': tested, 'word': bits}
    return {'status': 'no_fixedF_certificate_through_length',
            'max_length': max_length, 'tested_words': tested}
