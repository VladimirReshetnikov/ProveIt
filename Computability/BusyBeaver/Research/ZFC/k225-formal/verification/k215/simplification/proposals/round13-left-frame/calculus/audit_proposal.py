#!/usr/bin/env python3
"""Owned source/contract audit only. Does not execute received scripts or Lean/Rocq."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
if not __debug__:
    raise SystemExit('Run without -O: assertions implement this source audit.')
ROOT=Path(__file__).resolve().parent
pins=json.loads((ROOT/'INPUT_PINS.json').read_text())
assert pins['pin']=='6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95'
for name, rec in pins['files'].items():
    b=(ROOT/'inputs'/name).read_bytes()
    assert len(b)==rec['bytes']
    assert hashlib.sha256(b).hexdigest()==rec['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==rec['blob_sha1']
# Verify deterministic text construction using this packet's own reviewed builder.
products=['local_equality_capabilities.patch','PROPOSAL_METRICS.json']+[
    'proposed/'+n for n in ('TarskiDerived.lean','TarskiLeibniz.lean','KThmK.lean')]
old={n:(ROOT/n).read_bytes() for n in products}
subprocess.run([sys.executable,str(ROOT/'build_proposal.py')], check=True, stdout=subprocess.DEVNULL)
assert all((ROOT/n).read_bytes()==b for n,b in old.items()), 'Proposal drifted'

def headers(txt):
    out={}
    for m in re.finditer(r'(?m)^theorem ([A-Za-z0-9_]+)\b',txt):
        rest=txt[m.start():]
        ends=[i for tok in (':=', '\n  |') if (i:=rest.find(tok))>=0]
        end=min(ends)
        sig=re.sub(r'\s+',' ',rest[:end]).strip()
        out[m.group(1)]=sig
    return out

def imports(txt):return re.findall(r'(?m)^import .+$',txt)

checks={}
for fn in ('TarskiDerived.lean','TarskiLeibniz.lean','KThmK.lean'):
    a=(ROOT/'inputs'/fn).read_text();b=(ROOT/'proposed'/fn).read_text()
    ha,hb=headers(a),headers(b)
    assert ha.keys()<=hb.keys(),(fn,'lost theorem')
    assert all(hb[n]==sig for n,sig in ha.items()),(fn,'changed explicit signature')
    assert imports(a)==imports(b),(fn,'changed imports')
    # Non-admission source hygiene is not an axiom-profile or elaboration proof.
    assert not re.search(r'\b(sorry|admit|unsafe)\b|(?m:^axiom )',b)
    checks[fn]={'unchanged_explicit_theorem_headers':len(ha),'unchanged_imports':len(imports(a))}
# Alpha-renaming remains byte-for-byte unchanged, including guards and proof bodies.
for fn in ('TarskiLeibniz.lean','KThmK.lean'):
    a=(ROOT/'inputs'/fn).read_text();b=(ROOT/'proposed'/fn).read_text()
    assert a[a.index('theorem alpha_fwd'):]==b[b.index('theorem alpha_fwd'):]
L=(ROOT/'proposed'/'TarskiLeibniz.lean').read_text()
K=(ROOT/'proposed'/'KThmK.lean').read_text()
D=(ROOT/'proposed'/'TarskiDerived.lean').read_text()
assert '∀ i, Bound i f → T (imp (NF.eq x y) (all i (NF.eq x y)))' in L
assert '(fun _ hi => (qf_bound hq hi).elim)' in K
assert 'eq_refl_of_vac classical (Code254.wel x x) x (.helper x x)' in K
assert '(.vacEq x x (x + 1) (by omega) (by omega))' in D
assert '(ex_elim x (eqFree_rn x y f hf) (not_occurs_rn hxy f (qf_bound hq)))' in K
assert '  |' not in K[K.index('theorem leibniz'):K.index('/-- Specialization')] # No duplicated Leibniz induction.
# Both new compositional proof patterns have the expected boolean semantics.
count=0
for e in (False,True):
 for a in (False,True):
  for ap in (False,True):
   for b in (False,True):
    for bp in (False,True):
     imp=lambda x,y:(not x)or y
     h1=imp(e,imp(ap,a));h2=imp(e,imp(b,bp))
     assert not(h1 and h2) or imp(e,imp(imp(a,b),imp(ap,bp)))
     count+=1
metrics=json.loads((ROOT/'PROPOSAL_METRICS.json').read_text())
res={'status':'PASS_SOURCE_AUDIT_ONLY','pin':pins['pin'],'input_blobs_verified':len(pins['files']),
     'contracts':checks,'conditional_implication_boolean_cases':count,
     'prototype_totals':metrics['totals'],'kernel_compilation':'NOT_RUN_NO_TOOLCHAIN',
     'formal_assumption_report':'NOT_RUN','runtime_or_endpoint_changes':'NONE_IN_PROPOSAL'}
(ROOT/'AUDIT.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
