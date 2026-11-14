#!/usr/bin/env python3
"""Reproducible textual equation audit of two pinned Foundation sources.

This is not a Lean proof checker.  It compares constructor equations,
recursive equation lemma statements, and finite axiom templates after the
explicit whitespace/namespace/quantifier-notation normalization below.
The accompanying mathematical note proves the interpretation step.
"""
from pathlib import Path
import hashlib,json,re

BASE=Path(__file__).resolve().parent
NOW=BASE/'source'
OLD=BASE/'historical'

blob_checks=[]
for folder,manifest in [(NOW,'manifest.json'),(OLD,'historical_manifest.json')]:
    pins=json.loads((BASE/manifest).read_text())['source']
    for relative,expected in pins.items():
        raw=(folder/relative).read_bytes()
        got=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        assert got==expected,('source blob mismatch',relative,expected,got)
        blob_checks.append(str((folder/relative).relative_to(BASE)))

def normalize(s):
    s=s.replace('FFL.','LO.').replace('∀¹','∀⁰').replace('∃¹','∃⁰')
    return re.sub(r'\s+','',s)

def decl(s,name,kind='def',statement=False):
    m=re.search(r'\b'+kind+r'\s+'+re.escape(name)+r'(?=\s|\(|\{|:)',s)
    if not m: raise AssertionError(('missing',kind,name))
    if statement:
        end=s.index(':=',m.start())
    else:
        end=s.find('\n\n',m.start())
        if end<0: end=len(s)
    return s[m.start():end]

checks=[]
def check(name,a,b):
    equal=normalize(a)==normalize(b)
    checks.append({'name':name,'equal':equal,'current':a,'historical':b})
    if not equal: print('DIFFERENT',name)

def paired(relative):
    old=relative.replace('/Bootstrapping/','/Arithmetic/Bootstrapping/')
    return (NOW/relative).read_text(),(OLD/old).read_text()

term,oldterm=paired('Foundation/FirstOrder/Bootstrapping/Syntax/Term/Basic.lean')
form,oldform=paired('Foundation/FirstOrder/Bootstrapping/Syntax/Formula/Basic.lean')
proof,oldproof=paired('Foundation/FirstOrder/Bootstrapping/Syntax/Proof/Basic.lean')
for name in ['qqBvar','qqFvar','qqFunc','qqFuncN']:
    check(name,decl(term,name),decl(oldterm,name))
for name in ['qqRel','qqNRel','qqVerum','qqFalsum','qqAnd','qqOr','qqAll','qqExs']:
    check(name,decl(form,name),decl(oldform,name))
for name in ['termBV_bvar','termBV_fvar','termBV_func']:
    check(name,decl(term,name,'lemma',True),decl(oldterm,name,'lemma',True))
for name in ['bv_rel','bv_nrel','bv_verum','bv_falsum','bv_and','bv_or','bv_all','bv_ex']:
    check(name,decl(form,name,'lemma',True),decl(oldform,name,'lemma',True))
for name in ['axL','verumIntro','andIntro','orIntro','allIntro','exsIntro','wkRule','shiftRule','cutRule','axm']:
    check(name,decl(proof,name),decl(oldproof,name))
check('Derivation.Phi',decl(proof.split('namespace Derivation',1)[1],'Phi'),decl(oldproof.split('namespace Derivation',1)[1],'Phi'))
check('Proof',decl(proof,'Proof'),decl(oldproof,'Proof'))
check('DerivationOf',decl(proof,'DerivationOf'),decl(oldproof,'DerivationOf'))
check('mem_setShift_iff',decl(proof,'mem_setShift_iff','lemma',True),decl(oldproof,'mem_setShift_iff','lemma',True))
check('FormalizedTerm.Phi',decl(term.split('namespace FormalizedTerm',1)[1],'Phi'),decl(oldterm.split('namespace FormalizedTerm',1)[1],'Phi'))
check('FormalizedFormula.Phi',decl(form,'Phi'),decl(oldform,'Phi'))

for relative,names in [
    ('Foundation/FirstOrder/Bootstrapping/Syntax/Term/Functions.lean',
     ['termSubst_bvar','termSubst_fvar','termSubst_func','termSubstVec_nil','termSubstVec_cons',
      'termShift_bvar','termShift_fvar','termShift_func','termShiftVec_nil','termShiftVec_cons',
      'termBShift_bvar','termBShift_fvar','termBShift_func','termBShiftVec_nil','termBShiftVec_cons']),
    ('Foundation/FirstOrder/Bootstrapping/Syntax/Formula/Functions.lean',
     ['neg_rel','neg_nrel','neg_verum','neg_falsum','neg_and','neg_or','neg_all','neg_ex',
      'shift_rel','shift_nrel','shift_verum','shift_falsum','shift_and','shift_or','shift_all','shift_exs',
      'substs_rel','substs_nrel','substs_verum','substs_falsum','substs_and','substs_or','substs_all','substs_ex'])]:
    a,b=paired(relative)
    for name in names:
        check(name,decl(a,name,'lemma',True),decl(b,name,'lemma',True))

for relative,names in [
    ('Foundation/FirstOrder/Bootstrapping/Syntax/Term/Functions.lean',['qVec']),
    ('Foundation/FirstOrder/Bootstrapping/Syntax/Formula/Functions.lean',['imp','substs1','free']),
    ('Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean',['pair']),
]:
    a,b=paired(relative)
    for name in names: check(name,decl(a,name),decl(b,name))

for relative,marker in [
    ('Foundation/FirstOrder/Arithmetic/HFS/Vec.lean','lemma adjoin_def'),
    ('Foundation/Vorspiel/Matrix.lean','def vecToNat'),
]:
    a,b=paired(relative)
    kind,name=marker.split()
    aa,bb=decl(a,name,kind,kind=='lemma'),decl(b,name,kind,kind=='lemma')
    if name=='vecToNat':
        # The old local implicit binder became a surrounding variable.
        aa=aa.split(':=',1)[1];bb=bb.split(':=',1)[1]
    check(name,aa,bb)

bit,oldbit=paired('Foundation/FirstOrder/Arithmetic/Exponential/Bit.lean')
for name in ['Bit','bitInsert','bitRemove']:
    check(name,decl(bit,name),decl(oldbit,name))

lang,oldlang=paired('Foundation/FirstOrder/Bootstrapping/Syntax/Language.lean')
for suffix in ['func','rel']:
    pat=r'instance : \(ℒₒᵣ\)\.LORDefinable where\s+func := (.*?)\n  rel\s+:= (.*?)\n  func_iff'
    a=re.search(pat,lang,re.S); b=re.search(pat,oldlang,re.S)
    assert a and b
    i=1 if suffix=='func' else 2
    check('arithmetic_symbol_'+suffix,a.group(i),b.group(i))

eq=(NOW/'Foundation/FirstOrder/Basic/Eq.lean').read_text()
oldeq=(OLD/'Foundation/FirstOrder/Syntax/Classical/Eq.lean').read_text()
for name in ['Eq.refl','Eq.symm','Eq.trans','Eq.funcExt','Eq.relExt']:
    check(name,decl(eq,name,'abbrev'),decl(oldeq,name,'abbrev'))
axioms,oldaxioms=paired('Foundation/FirstOrder/Arithmetic/PeanoMinus/Basic.lean')
def finite_axioms(s):
    return dict(re.findall(r'^abbrev\s+(\w+)\s*:\s*ArithmeticSentence\s*:=\s*(.+)$',s,re.M))
a=finite_axioms(axioms);b=finite_axioms(oldaxioms)
assert set(a)==set(b) and len(a)==17
for name in a:
    if name!='addEqOfLt':check('PAminus.'+name,a[name],b[name])
changed={'name':'PAminus.addEqOfLt','current':a['addEqOfLt'],'historical':b['addEqOfLt']}
assert normalize(changed['current'])!=normalize(changed['historical'])

schemata,oldschemata=paired('Foundation/FirstOrder/Arithmetic/Schemata.lean')
for name in ['succInd','InductionScheme']:
    check(name,decl(schemata,name),decl(oldschemata,name))
for name in ['Peano']:
    check(name,decl(schemata,name,'abbrev'),decl(oldschemata,name,'abbrev'))

ind=(NOW/'Foundation/FirstOrder/Incompleteness/InductionSchemeDelta1.lean').read_text()
oldind=(OLD/'Foundation/FirstOrder/Incompleteness/Definability.lean').read_text()
olditer=(OLD/'Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Formula/Iteration.lean').read_text()
oldtyped=(OLD/'Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Typed.lean').read_text()
for name in ['qqAlls_zero','qqAlls_succ']:
    check(name,decl(ind,name,'lemma',True),decl(olditer,name,'lemma',True))
for name in ['fvarVec_zero','fvarVec_succ']:
    check(name,decl(ind,name,'lemma',True),decl(oldtyped,name,'lemma',True))
currentR=decl(ind,'InductionUnivR').split(':=',1)[1]
oldR=decl(oldind,'InductionR').split(':=',1)[1].replace(' ∧ S K','')
check('InductionUnivR = InductionR(True)',currentR,oldR)

receipt={
  'description':__doc__.strip(),
  'current_foundation_commit':'32e1a0956a8622fad067328ca1959729a7634428',
  'historical_proveit_commit':'1c9524d8bf2e0a27b9a16ff622359927f536e663',
  'normalization':['whitespace deletion','FFL namespace renamed LO','quantifier notation superscript1 renamed0','vecToNat comparison restricted to RHS because implicit n binder moved outside declaration','InductionR(True) removes the literal conjunct S K'],
  'checks':checks,'shared_equation_checks':sum(c['equal'] for c in checks),
  'pinned_blob_checks':len(blob_checks),
  'unequal_checks':[c['name'] for c in checks if not c['equal']],
  'finite_axiom_difference':changed,
  'source_sha256':{str(p.relative_to(BASE)):hashlib.sha256(p.read_bytes()).hexdigest()
                   for root in [NOW,OLD] for p in root.rglob('*.lean')},
}
(BASE/'comparison_receipt.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'pinned_blob_checks':receipt['pinned_blob_checks'],'shared_equation_checks':receipt['shared_equation_checks'],'unequal_checks':receipt['unequal_checks'],'finite_axiom_difference':changed},ensure_ascii=False,indent=2))
if receipt['unequal_checks']:
    raise SystemExit(1)
