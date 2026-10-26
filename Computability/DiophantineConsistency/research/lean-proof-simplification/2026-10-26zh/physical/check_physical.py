#!/usr/bin/env python3
"""Read-only, standalone evidence checker. No Lean execution; emits JSON to stdout."""
from pathlib import Path
import argparse
import difflib
import hashlib
import itertools
import json
import re
import sys
ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline-tree', type=Path, default=ROOT.parent / 'baseline')
args = parser.parse_args()
BASELINE = args.baseline_tree / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
errors = []
def require(ok, message):
    if not ok:
        errors.append(message)
def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()
def metrics(text):
    return dict(physical_lines=len(text.splitlines()),
        nonblank_lines=sum(bool(s.strip()) for s in text.splitlines()),
        bytes=len(text.encode()), sha256=digest(text))
def headers(text):
    return [s.split(':=')[0].strip() for s in
        re.findall(r'(?m)^(?:noncomputable )?(?:def|theorem|instance)\b[\s\S]*?(?=:=)',text)]
def block(text, start, end):
    return text[text.index(start):text.index(end,text.index(start))]
try:
    old=(BASELINE/'WangTiles942PhysicalOrder.lean').read_text()
    data=(BASELINE/'WangTiles942PhysicalData.lean').read_text()
    stored=json.loads((ROOT/'evidence/checks.json').read_text())
    require(digest(old)=='eafbd5914bf4219d6ce48b501c8be41c228253ef719b65a02e7d167ada0ce3e9','Wrong baseline order hash')
    require(digest(data)=='38a11d1ef8d3391074d4cd347e0f764417c6502afd9a6a064d54266456396f5b','Wrong baseline data hash')
    order_old=block(old,'theorem strictMono_fin_eq_self ','\ndef rankMap ')
    pred_old=block(old,'def nonStartIndex ','\ntheorem nonStartWeight_eq ')
    order_new='''theorem strictMono_fin_eq_self {n : ℕ} (f : Fin n → Fin n) (hf : StrictMono f)
    (i : Fin n) : f i = i := by
  let e : Fin n ≃o Fin n :=
    ⟨Equiv.ofBijective f
      ⟨hf.injective, Finite.surjective_of_injective hf.injective⟩, hf.le_iff_le⟩
  exact Fin.ext (Fin.coe_orderIso_apply e i)
'''
    pred_new='''def nonStartIndex (j : Fin 941) : Fin 941 :=
  (abstractIndex j).pred (abstractIndex_ne_zero j)

theorem nonStartIndex_succ (j : Fin 941) : (nonStartIndex j).succ = abstractIndex j :=
  Fin.succ_pred (abstractIndex j) (abstractIndex_ne_zero j)
'''
    candidates={
        'order_iso':old.replace(order_old,order_new),
        'fin_pred':old.replace(pred_old,pred_new),
        'combined':old.replace(order_old,order_new).replace(pred_old,pred_new),
    }
    rel='Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942PhysicalOrder.lean'
    for name,expected in candidates.items():
        actual=(ROOT/f'candidate/{name}/WangTiles942PhysicalOrder.lean').read_text()
        require(actual==expected,f'{name}: unexpected text outside authorized replacement')
        require(headers(actual)==headers(old),f'{name}: public header changed')
        require(metrics(actual)==stored['variants'][name],f'{name}: stale metrics')
        patch=''.join(difflib.unified_diff(old.splitlines(True),actual.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
        require(patch==(ROOT/f'patches/{name}.patch').read_text(),f'{name}: patch differs from exact candidate diff')
        require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',actual),f'{name}: forbidden marker')
    require(metrics(old)==stored['original'],'Stale baseline metrics')
    finite=[]
    for n in range(7):
        total=accepted=0
        for f in itertools.product(range(n),repeat=n):
            total+=1
            if all(f[i]<f[j] for i in range(n) for j in range(i+1,n)):
                accepted+=1
                require(all(f[i]==i for i in range(n)),f'Nonidentity strictly monotone endomap at n={n}')
        finite.append(dict(n=n,endomaps_checked=total,strict_mono_maps=accepted))
    require(finite==stored['finite_smoke_checks']['all_endomaps'],'Stale finite enumeration receipt')
    rows=[tuple(map(int,p)) for p in re.findall(r'^  \((\d+), (\d+)\)',data,re.M)]
    require(len(rows)==941,'Wrong row count')
    require({i for i,w in rows}==set(range(1,942)),'Wrong literal index coverage')
    require(all(rows[k][1]>rows[k+1][1] for k in range(len(rows)-1)),'Unsorted literal coefficients')
    require(all(0<=i-1<941 and i-1+1==i for i,w in rows),'Bad finite predecessor recovery')
    for snapshot,receipt in [('mathlib_fin_basic.lean','mathlib_fin_basic_receipt.json'),('lean_fin_basic.lean','lean_fin_basic_receipt.json')]:
        data_bytes=(ROOT/'evidence'/snapshot).read_bytes()
        source_receipt=json.loads((ROOT/'evidence'/receipt).read_text())
        git_blob=hashlib.sha1(b'blob '+str(len(data_bytes)).encode()+b'\0'+data_bytes).hexdigest()
        require(git_blob==source_receipt['blob_sha'],f'{snapshot}: GitHub source blob mismatch')
    core=(ROOT/'evidence/lean_fin_basic.lean').read_text()
    require('def pred {n : Nat}' in core and 'subNat 1 i' in core,'Missing core pred definition evidence')
    require('⟨i - m, Nat.sub_lt_right_of_lt_add h i.2⟩' in core,'Core subNat value is not expected subtraction')
    regression=(ROOT/'candidate/PhysicalOrderRegressionChecks.lean').read_text()
    require('omega⟩ := rfl' in regression,'Missing rfl regression for the original constructor')
except (OSError,ValueError,KeyError,TypeError) as exc:
    errors.append(f'{type(exc).__name__}: {exc}')
result={'status':'PASS' if not errors else 'FAIL','errors':errors,
    'scope':'Static exact-text/patch/hash/count checks plus finite Python smoke checks; not Lean elaboration or kernel checking.',
    'lean_status':'NOT RUN','mutates_files':False}
print(json.dumps(result,indent=2))
sys.exit(0 if not errors else 1)
