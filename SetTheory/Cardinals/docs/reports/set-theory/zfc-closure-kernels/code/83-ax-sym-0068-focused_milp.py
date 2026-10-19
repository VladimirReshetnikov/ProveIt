#!/usr/bin/env python3
"""One finite-dictionary source optimization of a changed logical AX row.

Original control atoms are fixed. Objective counts source sequence phrases,
not binary states. The proposed row swaps the a,b schema roles in rho8.
"""
from pathlib import Path
import sys,json,random
from hashlib import sha256
import seeded_order as s
ROOT=s.ROOT
LAYOUT=Path(__file__).resolve().parent
sys.path.insert(0,str(LAYOUT))
import milp_dictionary as d
OUT=Path(__file__).with_name('focused_milp_results');OUT.mkdir(exist_ok=True)
d.HERE=OUT
candidate=json.loads((Path(__file__).with_name('novel_candidates')/'candidate_1_202.json').read_text())
word=tuple(candidate['ax_word'])
new=tuple(d.canonical(s.atom_edges[i]) for i in word)
old=max(d.required,key=len)
assert len(old)==len(new)==1270 and old!=new
changed_labels=[i for i,k in d.labels.items() if k==('S',old)]
assert len(changed_labels)==1
for i in changed_labels:d.labels[i]=('S',new)
d.required.remove(old);d.required.add(new);d.oldwords.add(new)
# Provide a complete fallback parse of the new required word as a finite
# dictionary seed. Every atom is still the original fixed program atom.
positions=[0]
for e in candidate['ax_pieces']:
 es=tuple(e);positions.append(positions[-1]+len(s.flat(es)))
assert positions[-1]==len(new)
d.extra_words={new[i:j] for i in positions for j in positions if j-i>=2}
# Seed the source201 association phrases, independently as exact words.
for i,w in s.words_by_node.items():
 translated=tuple(d.canonical(s.atom_edges[k]) for k in w)
 if len(translated)>1:d.extra_words.add(translated)
meta=dict(scope='One changed logical schema role assignment; finite ordered phrase dictionary with source201 seeds, zero-run<=7, depth<=64; source-node objective only',order=candidate['order'],roles=candidate['roles'],u_b_swap=False,expected_long_word=1270,old_long_word=old,new_long_word=new,extra_phrases=len(d.extra_words),dictionary_driver_sha256=sha256((LAYOUT/'milp_dictionary.py').read_bytes()).hexdigest(),candidate_input_sha256=sha256((Path(__file__).with_name('novel_candidates')/'candidate_1_202.json').read_bytes()).hexdigest())
(OUT/'specification.json').write_text(json.dumps(meta,indent=2)+'\n')
d.run(maxlen=24,minfreq=2,seconds=120,maxzeros=7,maxdepth=64,prefer_old=True)
