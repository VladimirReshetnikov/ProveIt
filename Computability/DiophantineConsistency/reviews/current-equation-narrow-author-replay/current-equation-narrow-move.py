from pathlib import Path
import json,hashlib,re,subprocess
root=Path('/home/codex/.codex/worktrees/46be/Proofs');d=root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
old=['LowMaskCoding','WangTiles942Core','CurrentMasks2011','CurrentKernel2011','CurrentWindowCarry2011','ObjectCurrentEquation2011','ArithmeticCurrentEquation2011']
sources={n:(d/(n+'.lean')).read_text() for n in old}; changes={n:[] for n in old}; entries=[]
def h(s):return hashlib.sha256(s.encode()).hexdigest()
def grab(owner,name):
 s=sources[owner]; matches=list(re.finditer(r'^(?:def|abbrev|structure|theorem|irreducible_def) '+re.escape(name)+r'(?=\s|\()',s,re.M));assert len(matches)==1,(owner,name)
 a=matches[0].start();b=s.find('\n\n',a);assert b>=0
 nxt=re.search(r'^((?:def|abbrev|structure|theorem|irreducible_def) )',s[matches[0].end():],re.M)
 if nxt:b=min(b,matches[0].end()+nxt.start()-1)
 before=s[:a].rstrip()
 if before.endswith('-/'):
  c=before.rfind('/--')
  if c>=0 and '/-' not in before[c+3:]:a=c
 text=s[a:b]
 changes[owner].append((a,b));entries.append(dict(owner=owner,name=name,text=text,sha256=h(text)))
 return text
files={}
files['LowMaskData']='''import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The exact sparse-mask data, separated from its arithmetic coding proofs. -/
set_option Elab.async false
namespace DiophantineConsistency.LowMaskCoding
open scoped BigOperators

'''+ '\n\n'.join(grab('LowMaskCoding',x) for x in ['supportValue','mask'])+'\n\nend DiophantineConsistency.LowMaskCoding\n'
files['WangTiles942TableData']='''import DiophantineConsistency.WangTiles942Data
import Mathlib.Algebra.BigOperators.Fin

/-! The exact current row data and physical ranking, without broad tactic imports.
The two finite-list proofs retain the original checked definition of `tile`. -/
namespace DiophantineConsistency.WangTiles942
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

'''+ '\n\n'.join(grab('WangTiles942Core',x) for x in ['Tile','headColor','start','transitionRow','copyRows','signalRows','tailRows','indexedRows','orderedRows','row_indices_exact','ordered_count','tile','selectorWeight','physicalPosition'])+'\n\nend DiophantineConsistency.WangTiles942\n'
files['CurrentMaskData2011']='''import DiophantineConsistency.LowMaskData
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IrreducibleDef

/-! Exact current mask data; no source-window, population or machine premise. -/
namespace DiophantineConsistency.CurrentMasks2011
open LowMaskCoding
set_option Elab.async false

'''+ '\n\n'.join(grab('CurrentMasks2011',x) for x in ['radix','width','beta','lowSupport','lowPort','highPrefix','highDigits','highPort','ports'])+'\n\nend DiophantineConsistency.CurrentMasks2011\n'
files['CurrentKernelData2011']='''import DiophantineConsistency.WangTiles942TableData
import DiophantineConsistency.CurrentMaskData2011
import Mathlib.Data.Fintype.Sum

/-! Exact current finite kernel and complete four-port tuple, without native proofs. -/
namespace DiophantineConsistency.CurrentKernel2011
open WangTiles942
open scoped BigOperators
set_option Elab.async false

'''+ '\n\n'.join(grab('CurrentKernel2011',x) for x in ['radix','Entry','position','weight','Term','exponent','coefficient','rawWord','K'])+'''\n\nend DiophantineConsistency.CurrentKernel2011

namespace DiophantineConsistency.CurrentWindowCarry2011
open CurrentKernel2011

'''+grab('CurrentWindowCarry2011','ports')+'\n\nend DiophantineConsistency.CurrentWindowCarry2011\n'
files['CurrentEquationSyntax2011']='''import DiophantineConsistency.CurrentKernelData2011
import DiophantineConsistency.ArithmeticExpression

/-! The maintained literal expression and HA sentence, with their original names.
Only definition ownership changes; wide native and object semantics remain separate. -/
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ObjectCurrentEquation2011

'''+ '\n\n'.join(grab('ObjectCurrentEquation2011',x) for x in ['expressionAt','expression','positiveShift','naturalExpression'])+'''\n\nend DiophantineConsistency.ObjectCurrentEquation2011

namespace DiophantineConsistency.ArithmeticCurrentEquation2011
open SetTheory.PA ObjectCurrentEquation2011

'''+grab('ArithmeticCurrentEquation2011','unsolvabilitySentence')+'\n\nend DiophantineConsistency.ArithmeticCurrentEquation2011\n'
imports=dict(LowMaskCoding='LowMaskData',WangTiles942Core='WangTiles942TableData',CurrentMasks2011='CurrentMaskData2011',CurrentKernel2011='CurrentKernelData2011',CurrentWindowCarry2011='CurrentKernelData2011',ObjectCurrentEquation2011='CurrentEquationSyntax2011',ArithmeticCurrentEquation2011='CurrentEquationSyntax2011')
# Refuse duplicate or overlapping moves and preserve every other source byte.
for n,spans in changes.items():
 spans.sort();assert all(a>=b for (_,b),(a,_) in zip(spans,spans[1:])),n
 s=sources[n]
 for a,b in reversed(spans):s=s[:a]+s[b:]
 files[n]='import DiophantineConsistency.'+imports[n]+'\n'+s
p=Path('/tmp/current-equation-narrow-move-originals');assert not p.exists();p.mkdir()
for n,s in sources.items():(p/(n+'.lean')).write_text(s)
for n,s in files.items():(d/(n+'.lean')).write_text(s)
manifest=dict(snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),old_sources=[dict(module=n,old_sha256=h(s),snapshot=str(p/(n+'.lean')),new_sha256=h(files[n])) for n,s in sources.items()],moves=entries,new_sources=[dict(module=n,sha256=h(s)) for n,s in files.items() if n not in sources],driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(p/'move-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({k:len(v.splitlines()) for k,v in files.items()},indent=2));print('EXACT MOVES',len(entries))
