"""Generate Compact44/Facts/<File>.lean: LeafFacts copies of the halting-chain forwarders.

Each forwarder theorem NAME (whose literal-zero hypothesis hz is only passed
on) is copied as NAME_facts in the same namespace, with
  * hz : InternalZero (literal (fun j => (P j:ℤ))) v   ->   hz : LeafFacts (P) v
  * forwarder calls redirected to their _facts copies,
  * the six leaf calls replaced by field projections of hz.
Originals are not modified. Writes facts.queue (build order) next to this script.
"""
import os, re, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
D = r'C:\ProveIt\Computability\DiophantineConsistency\Lean\DiophantineConsistency\Compact44'
OUT = os.path.join(D, 'Facts')
LEAVES = {'FreeJExactOrdinary.exact_ordinary_indices', 'FreeJFirstTransport.freej_first_factor_transport',
          'FreeJGraphCongruenceExplore.first_pair_mod', 'FreeJPowerFinish.graph_power',
          'FreeJPowerProjection.graph_projection', 'FreeJRootBinding.first_scaled_norm'}
INTERNAL = {'FreeJExactTransport.first_quotient', 'FreeJPowerGrowth.growth', 'FreeJPowerGrowth.X_lower',
            'FreeJRootBinding.first_root_quotient', 'FreeJRootBinding.first_factor_forces_Y_divisible'}
decl = re.compile(r'^(?:private )?theorem (\w+)', re.M)
stop = re.compile(r'^(?:theorem|private theorem|lemma|def|private def|abbrev|structure|instance|#print|end |namespace|section|/--|/-!|@\[|set_option|open|variable|attribute|noncomputable)', re.M)

files = {}
for f in os.listdir(D):
    if f.endswith('.lean'):
        files[f[:-5]] = open(os.path.join(D, f), encoding='utf-8').read()

def namespace(t):
    m = re.findall(r'^namespace ([\w.]+)', t, re.M)
    return m[0] if m else ''

# theorem table: qualified short name -> (file, start, end, text)
thm = {}
for mod, t in files.items():
    ns = namespace(t).split('.')[-1]
    for m in decl.finditer(t):
        s = m.start()
        nxt = stop.search(t, m.end())
        e = nxt.start() if nxt else len(t)
        thm[ns + '.' + m.group(1)] = (mod, s, e, t[s:e])

hzthm = {k for k, (_, _, _, body) in thm.items()
         if re.search(r'\(hz : InternalZero \(literal', body.split(':= by')[0] if ':= by' in body else body)}

forward = [l.strip() for l in open(os.path.join(HERE, 'forwarders.txt'), encoding='utf-8-sig') if l.strip()]
assert all(k in hzthm for k in forward), [k for k in forward if k not in hzthm]
print('forwarders:', len(forward))

leafsubs = [
    (r'\((?:FreeJFirstTransport\.)?freej_first_factor_transport\s+p\s+v\s+(\w+)\s+hv\s+hz\)\.2', r'(hz.transport \1)'),
    (r'(?:FreeJGraphCongruenceExplore\.)?first_pair_mod\s+p\s+v\s+(\w+)\s+hv\s+hz', r'hz.pairMod \1'),
    (r'(?:FreeJExactOrdinary\.)?exact_ordinary_indices\s+p\s+v\s+(\w+)\s+(\w+)\s+(\w+)\s+hv\s+hz', r'hz.indices \1 \2 \3'),
    (r'\(?(?:FreeJPowerProjection\.)?graph_projection\s+p\s+v\s+(\w+)\s+(\w+)\s+(\w+)\s+hv\s+hz\)?', r'(hz.projection \1 \2 \3)'),
    (r'(?:FreeJPowerFinish\.)?graph_power\s+p\s+v\s+(\w+)\s+(\w+)\s+(\w+)\s+hv\s+hz\s+(\w+)', r'hz.power \1 \2 \3 \4'),
    (r'(?:FreeJRootBinding\.)?first_factor_forces_Y_divisible\s+p\s+v\s+hz\s+(\(hv 0\)|\w+)\s+(\w+)', r'hz.ydiv \1 \2'),
]
hzbind = re.compile(r'\(hz : InternalZero \(literal \(fun j => \((.+?) j:ℤ\)\)\) v\)')

bymod = {}
for k in forward:
    bymod.setdefault(thm[k][0], []).append(k)
fwdnames = {k.split('.')[1]: k for k in forward}

def transform(k):
    mod, s, e, body = thm[k]
    ns, name = k.split('.')
    head, sep, rest = body.partition(':= by') if ':= by' in body else body.partition(':=')
    head = hzbind.sub(lambda m: f'(hz : CompactLeafFacts.LeafFacts ({m.group(1)}) v)', head)
    head = re.sub(r'^((?:private )?theorem )' + name + r'\b', r'\g<1>' + name + '_facts', head)
    for pat, rep in leafsubs:
        rest = re.sub(pat, rep, rest)
    for other in forward:
        ons, oname = other.split('.')
        rest = re.sub(r'\b' + re.escape(ons) + r'\.' + oname + r'\b(?!_facts)', ons + '.' + oname + '_facts', rest)
        if ons == ns:
            rest = re.sub(r'(?<![\w.])' + oname + r'\b(?!_facts)', oname + '_facts', rest)
    out = head + sep + rest
    assert 'InternalZero (literal' not in head, k
    return out.rstrip() + '\n'

def preamble(t):
    first = decl.search(t).start()
    keep = []
    for line in t[:first].split('\n'):
        if re.match(r'^(set_option|noncomputable section|namespace|open|attribute|variable)', line):
            keep.append(line)
    return keep

os.makedirs(OUT, exist_ok=True)
imp = re.compile(r'^import ', re.M)
order = []
modset = set(bymod)
def deps_of(mod):
    ds = set()
    for k in bymod[mod]:
        body = transform(k)
        for other in forward:
            om = thm[other][0]
            if om != mod and (other.split('.')[0] + '.' + other.split('.')[1] + '_facts') in body:
                ds.add(om)
    return ds
mdeps = {m: deps_of(m) for m in bymod}
mark = set()
def topo(m):
    if m in mark: return
    mark.add(m)
    for d in sorted(mdeps[m]): topo(d)
    order.append(m)
for m in sorted(bymod): topo(m)
for mod in order:
    t = files[mod]
    lines = ['import DiophantineConsistency.Compact44.' + mod,
             'import DiophantineConsistency.Compact44.CompactLeafFacts']
    lines += ['import DiophantineConsistency.Compact44.Facts.' + d for d in sorted(mdeps[mod])]
    lines += ['', f'/-! `LeafFacts` copies of the forwarders of `{mod}` (generated by factsgen.py;',
              '    each proof is the original with `hz` retyped and leaf calls projected). -/']
    lines += preamble(t)
    body = [transform(k) for k in sorted(bymod[mod], key=lambda k: thm[k][1])]
    lines += [''] + body
    ns = namespace(t)
    lines += [f'#print axioms {ns}.{k.split(".")[1]}_facts' for k in sorted(bymod[mod], key=lambda k: thm[k][1])]
    if ns:
        lines.append(f'end {ns}')
    open(os.path.join(OUT, mod + '.lean'), 'w', encoding='utf-8', newline='\n').write('\n'.join(lines) + '\n')
open(os.path.join(HERE, 'facts.queue'), 'w', encoding='utf-8').write(
    '\n'.join('+DiophantineConsistency.Compact44.Facts.' + m for m in order) + '\n')
json.dump({'forwarders': forward, 'modules': order}, open(os.path.join(HERE, 'facts.json'), 'w'), indent=1)
print('modules:', len(order))
