#!/usr/bin/env python3
"""Owned, tightly scoped inspection of existing left-moving scanner paths.

No received code is imported. This does not synthesize or certify a repair.
"""
from pathlib import Path
import collections
import hashlib
import json

D = Path(__file__).resolve().parent
ROOT = D.parent
H = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
P = ROOT / 'latest218_baseline/candidate-k218/k218.native.tm'
assert H(P) == '2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
T = {}
for line in P.read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,n = line.split()
        T[int(q),int(b)] = (int(w), 1 if d == 'R' else -1, int(n))
assert [T[k] for k in [(87,0),(88,0),(51,0),(301,0),(301,1)]] == [
    (0,1,301),(0,1,122),(0,1,16),(0,1,45),(1,1,103)]
T = {k:v for k,v in T.items() if k[0] != 301}
T.update({(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122)})
assert len(T) == 434 and len({q for q,b in T}) == 217
text = '#! start 0\n' + ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
    for (q,b),(w,d,n) in sorted(T.items()))
outtable = D / 'initialized217.native.tm'
outtable.write_text(text)

binding = json.loads((D/'NEW_CONTEXT_BINDING.json').read_text())
contexts = [dict(kind='boot', name=f'boot_at_{e["step"]}',
                 ones=set(e['relative_ones']), lo=None, hi=None)
            for e in binding['boot_exceptions']]
for e in binding['decoder_prefix_events']:
    h=e['head'];pc=e['site'][0]
    ones={-1}|{i for i,b in enumerate(pc) if b=='1'}
    contexts.append(dict(kind='decoder', name=f'site_{e["source_index"]}',
                         ones={p-h for p in ones},lo=None,hi=39-h))

entries = [1,2,3,5,9,15,23,34,50,40,54,13,62,63,76,152,157]
assert all(T[q,b][1] == -1 for q in entries for b in (0,1))
results = []
for entry in entries:
    traces = []
    for c in contexts:
        # Proposed entry 51/0 = 0 L entry; its write is nondestructive.
        q,h = entry,-1
        trace, seen = [],set()
        for step in range(100):
            if (c['lo'] is not None and h<c['lo']) or (c['hi'] is not None and h>c['hi']):
                stop='LEAVES_KNOWN_WINDOW';break
            b = int(h in c['ones'])
            if c['kind']=='boot' and T[q,b][0]==b and T[q,b][2]==q and ((T[q,b][1]==1 and h>max(c['ones'])) or (T[q,b][1]==-1 and h<min(c['ones']))):
                stop='EXACT_OUTWARD_BLANK_RAY';break
            if (q,h) in seen:
                stop='READ_ONLY_EXACT_CYCLE';break
            seen.add((q,h))
            w,d,n = T[q,b]
            trace.append([q,h,b,w,d,n])
            if w != b:
                stop='FIRST_TAPE_CHANGE';break
            if q == 84:
                stop='GLOBAL_DISPATCH_NOT_LOCAL_RESTORATION';break
            q,h = n,h+d
        else: stop='100_STEP_INSPECTION_BOUND'
        traces.append(dict(context=c['name'],kind=c['kind'],stop=stop,
                           min_read_head=min(t[1] for t in trace),trace=trace))
    results.append(dict(entry=entry, outcomes=dict(collections.Counter(t['stop'] for t in traces)),
                        traces=traces))
receipt = dict(status='SCOPED_EXISTING_PATH_INSPECTION_NOT_A_REPAIR_SEARCH',
    parent_sha256=H(P), composed217_sha256=H(outtable), row_count=len(T), working_states=217,
    contexts=len(contexts), boot_contexts=5, decoder_contexts=len(contexts)-5,
    new_context_binding_sha256=H(D/'NEW_CONTEXT_BINDING.json'), entries=entries, results=results,
    scope='Literal read-only path inspection until first changed bit, known-window exit, '
          'global dispatch, exact read-only cycle, or 100 steps. No blanket rejection '
          'of destructive-then-restoring helpers. Decoder inputs are freshly extracted '
          'from every new source prefix; the boot tapes are exact new218 snapshots.')
(D/'SCANNER_PATH_INSPECTION.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))
for r in results:
    print(r['entry'],r['outcomes'])
    print('  first boot:',r['traces'][0]['stop'],'last row',r['traces'][0]['trace'][-1])
