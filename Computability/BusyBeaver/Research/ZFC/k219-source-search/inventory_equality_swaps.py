#!/usr/bin/env python3
"""All sixteen equality hits, with and without comparator-only 5/6 exchange.

Source/CFG and generic leaf-entry inventory only; no candidate allocation.
Seven hit contracts have separate ordinary proofs. Other submitted hits
remain finite-tested historical candidates, not all-natural certified.
"""
from model import *
import argparse, importlib, sys, time

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output', type=Path, required=True)
args = ap.parse_args()
assert __debug__ and not args.output.exists()
sys.dont_write_bytecode = True
library = HERE.parent / 'k219-continuation-search/compiler-inputs'
pins = {'source_language.py': '4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
        'build221.py': '3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba'}
for name, value in pins.items():
    assert hashlib.sha256((library/name).read_bytes()).hexdigest() == value
sys.path.insert(0, str(library))
s = importlib.import_module('source_language')
b = importlib.import_module('build221')
oldrows = json.loads((BASE/'sites219.json').read_text())
tree = s.tree(oldrows)
assert hashlib.sha256((BASE/'sites219.json').read_bytes()).hexdigest() == '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
assert hashlib.sha256((BASE/'k219.native.tm').read_bytes()).hexdigest() == 'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
assert hashlib.sha256(HITS.read_bytes()).hexdigest() == '6b9a424830dd28216c6b20524900d01faac832d4b80bc9147eb03c0ce86f7c6b'
table = b.read_table((BASE/'k219.native.tm').read_bytes())
groups, _ = b.decoder_map(table, tree)
old_states = collections.defaultdict(set)
for q, ns in groups.items():
    for n in ns:
        old_states[n].add(q)
generic = {}
for op in ('CI', 'CD', 'CC', 'CB', 'CH'):
    for arg in ([None] if op == 'CH' else range(10)):
        ch = op, arg
        for bit in (0, 1):
            choices = {table[q, bit] for n, qs in old_states.items() for q in qs if n[bit] == ch}
            direct = [a for a in choices if a[:2] == (bit, 1)]
            if len(direct) == 1:
                generic[ch, bit] = direct[0]
            elif bit == 1 and ch in (('CC', 1), ('CC', 2), ('CB', 1)):
                generic[ch, bit] = {('CC', 1): (0, -1, 1), ('CC', 2): (0, -1, 16), ('CB', 1): (0, -1, 40)}[ch]
hits = list(map(freeze, json.loads(HITS.read_text())))
assert len(hits) == 16
accepted = hits[10]
proved = {0, 1, 2, 3, 10, 11, 12}
def swap(n):
    if leaf(n):
        op, arg = n
        return op, 11-arg if op in ('CI', 'CD') and arg in (5, 6) else arg
    return swap(n[0]), swap(n[1])
def substitute(t, h, path='', paths=None):
    if t == accepted:
        paths.append(path)
        return h
    return t if leaf(t) else (substitute(t[0],h,path+'0',paths),substitute(t[1],h,path+'1',paths))
args.output.mkdir(parents=True)
(args.output/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
records = []; started = time.monotonic()
for i, h in enumerate(hits):
    assert all(op not in ('CI', 'CD') or arg in (5, 6) for _, op, arg in leaves(h))
    assert swap(swap(h)) == h
    for exchanged in (False, True):
        macro = swap(h) if exchanged else h
        paths = []; full = substitute(tree, macro, paths=paths)
        assert len(paths) == 4
        rr = leaves(full)
        assert graph(rr) == arithmetic_graph(rr)
        fresh_nodes = [n for n in nodes(full) if not leaf(n) and n not in old_states]
        missing = collections.Counter()
        for n in fresh_nodes:
            for bit, ch in enumerate(n):
                if leaf(ch) and (ch, bit) not in generic:
                    missing[ch, bit] += 1
        name = f'hit{i:02d}' + ('-swap56' if exchanged else '-original')
        raw = (json.dumps(rr,separators=(',',':'))+'\n').encode()
        (args.output/(name+'.sites.json')).write_bytes(raw)
        rec = dict(name=name, hit=i, swap56=exchanged, source_sha256=hashlib.sha256(raw).hexdigest(),
                   metrics=metrics(full), new_interior_nodes=len(fresh_nodes),
                   missing_generic_edges=[dict(op=ch[0],arg=ch[1],bit=bit,count=count) for (ch,bit),count in sorted(missing.items())],
                   source_contract='ordinary all-natural proof' if i in proved else 'historical finite tests only',
                   replaced_paths=paths, cfg_resolvers_agree=True)
        records.append(rec)
        print(name,rec['metrics']['dag_nodes'],rec['new_interior_nodes'],rec['missing_generic_edges'],flush=True)
result = dict(status='ALL32_SOURCE_AND_ENTRY_INVENTORIES_PASS', records=records,
              inputs=dict(source='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789',table='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26',hits='6b9a424830dd28216c6b20524900d01faac832d4b80bc9147eb03c0ce86f7c6b',compiler_utilities=pins),
              minimum_source_dag=min(r['metrics']['dag_nodes'] for r in records),
              scope='Source metrics, complete CFG agreement and generic-entry needs at new internal nodes only. Origin-reuse may retain a context-specific old entry, so a missing generic edge is not itself a compiler rejection. No candidate compiler or runtime was invoked. Swapping counters preserves each proven symmetric clean equality contract; it does not prove unproved hits.',
              script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),seconds=time.monotonic()-started)
(args.output/'result.json').write_text(json.dumps(result,indent=2)+'\n')
