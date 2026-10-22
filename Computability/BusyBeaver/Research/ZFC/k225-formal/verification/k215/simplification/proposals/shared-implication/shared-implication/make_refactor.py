#!/usr/bin/env python3
"""Render a review-only shared implicational basis patch against pinned ProveIt.

This script reads the checkout and writes only OUTPUT, never the checkout.
Usage: python make_refactor.py CHECKOUT OUTPUT
"""
from pathlib import Path
import sys, difflib, hashlib, importlib.util, json
repo=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();out.mkdir(parents=True,exist_ok=True)
root=Path('Computability/BusyBeaver')
research=root/'Research/ZFC/k225-formal/rho8cd'
lean=root/'Lean/BusyBeaver/ZFC'
genrel=research/'generate_domrho8_cd.py';derrel=research/'derivation_core.txt';corerel=lean/'DominatedImplication.lean';lukrel=lean/'Lukasiewicz.lean'
gen=(repo/genrel).read_text();der=(repo/derrel).read_text();luk=(repo/lukrel).read_text()
assert '# Dominated rho8, composition and prefixing by condensed detachment, without truth: 58 steps' in der
assert luk.count('private theorem cd_')==107

der=der.replace('without truth: 58 steps','without truth: 63 steps')
der += '''# Five extra modus-ponens steps expose the S basis already needed by Lukasiewicz.lean.
# K and Peirce are existing nodes 12 and 18; no additional steps are needed for them.
#GOAL 12 (a>(b>a))
#GOAL 18 (((a>b)>a)>a)
#GOAL 67 ((a>(b>c))>((a>b)>(a>c)))
63 62 37 ((((a>b)>b)>c)>(a>c)) []
64 62 62 ((((a>b)>(c>b))>d)>((c>a)>d)) []
65 64 48 ((a>b)>((a>(b>c))>(a>c))) []
66 64 63 ((a>(b>c))>(b>(a>c))) []
67 66 65 ((a>(b>c))>((a>b)>(a>c))) []
'''
gen=gen.replace("PREFIX = parse('((a>b)>((c>a)>(c>b)))')", "PREFIX = parse('((a>b)>((c>a)>(c>b)))')\nK_BASIS = parse('(a>(b>a))')\nPEIRCE = parse('(((a>b)>a)>a)')\nS_BASIS = parse('((a>(b>c))>((a>b)>(a>c)))')")
old="[(COMPOSITION, ['a', 'b', 'c']), (PREFIX, ['a', 'b', 'x'])]"
new="[(COMPOSITION, ['a', 'b', 'c']), (PREFIX, ['a', 'b', 'x']),\n                         (K_BASIS, ['a', 'b']), (PEIRCE, ['a', 'b']),\n                         (S_BASIS, ['a', 'b', 'c'])]"
assert old in gen;gen=gen.replace(old,new)
gen=gen.replace('row=use[ROW], composition=use.get(COMPOSITION), prefix=use.get(PREFIX))','row=use[ROW], composition=use.get(COMPOSITION), prefix=use.get(PREFIX),\n        k=use.get(K_BASIS), peirce=use.get(PEIRCE), s=use.get(S_BASIS))')
old='''end
#print axioms rho8_all
#print axioms composition
#print axioms lift_right
end SetTheory.BusyBeaver.ZFC.DominatedImplication'''
new='''/-- The K basis is already node 12 of the shared derivation. -/
theorem k (a b : A) : T (L.imp a (L.imp b a)) :=
  {k}

/-- Peirce is already node 18 of the shared derivation. -/
theorem peirce (a b : A) : T (L.imp (L.imp (L.imp a b) a) a) :=
  {peirce}

/-- S follows using five additional modus-ponens steps. -/
theorem s (a b c : A) :
    T (L.imp (L.imp a (L.imp b c)) (L.imp (L.imp a b) (L.imp a c))) :=
  {s}

end
#print axioms rho8_all
#print axioms composition
#print axioms lift_right
#print axioms k
#print axioms peirce
#print axioms s
end SetTheory.BusyBeaver.ZFC.DominatedImplication'''
assert old in gen;gen=gen.replace(old,new)
gen=gen.replace('the unrestricted row, composition and\nprefixing from modus ponens', 'the unrestricted row, composition, prefixing and the K/Peirce/S basis from modus ponens')

def write(rel,text):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
write(genrel,gen);write(derrel,der)
spec=importlib.util.spec_from_file_location('renderer',out/genrel);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
rows,goals=m.read(out/derrel);core=m.render(rows,goals,'core');write(corerel,core)

start=luk.index('/-- Source certificates list the minor premise')
end=luk.index('\nend SetTheory.BusyBeaver.ZFC.Lukasiewicz',start)
wrapper='''/-- Unrestricted rows instantiate the shared core with the always-true guard. -/
private def fullLanguage (imp : α → α → α) : DominatedImplication.Language α where
  imp := imp
  below := fun _ _ => True
  refl := fun _ => True.intro
  grow_left := fun _ _ => True.intro
  grow_right := fun _ _ => True.intro

private theorem restricted (h : Implicational imp T) :
    DominatedImplication.Restricted (fullLanguage imp) T where
  mp := h.mp
  rho8 := fun a b c u _ => h.rho8 c u a b

/-- K follows from rho8 alone, through the shared core. -/
theorem k (h : Implicational imp T) (a b : α) : T (imp a (imp b a)) :=
  DominatedImplication.k (restricted h) a b

/-- Peirce follows from rho8 alone, through the shared core. -/
theorem peirce (h : Implicational imp T) (a b : α) :
    T (imp (imp (imp a b) a) a) :=
  DominatedImplication.peirce (restricted h) a b

/-- Implication composition, through the shared core. -/
theorem composition (h : Implicational imp T) (a b c : α) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) :=
  DominatedImplication.composition (restricted h) a b c

/-- S follows from rho8 alone, through the shared core. -/
theorem s (h : Implicational imp T) (a b c : α) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) :=
  DominatedImplication.s (restricted h) a b c
'''
newluk=luk[:start]+wrapper+luk[end:]
newluk=newluk.replace('import BusyBeaver.ZFC.TarskiComplete','import BusyBeaver.ZFC.TarskiComplete\nimport BusyBeaver.ZFC.DominatedImplication',1)
headstart=newluk.index('/-!');headend=newluk.index('-/',headstart)+2
header='''/-!
The shared implicational basis and unconditional Tarski logic bridge.

The generic K, S, Peirce and composition theorems now instantiate the
representation-independent DominatedImplication core with the always-true
side condition. The old 107-certificate port from Jeff's CD254.v is replaced
by four adapters; the shared core's 58-step derivation gains five MP steps
for S. This preserves the public interface and the Tarski bridge below.

Historical attribution: the replaced certificates ported Jeff's ZF/m254/coq/logic/CD254.v
at busy-beaver commit 297ab8df7e5de329605c3875b4934643b371a5e3 (Mira-Cult's
machine; Jeff's verification). See the pinned parent for the complete historical source.
The replacement core is regenerated from k225-formal/rho8cd/derivation_core.txt;
every inference is checked by the Lean kernel, without assumptions about decoding,
implication injectivity, truth, falsity, or the search program.

Ex falso additionally uses rho6 with the original NF.bot-relative existential.
This file concerns named syntax; it does not assert a machine consistency endpoint.
-/'''
newluk=newluk[:headstart]+header+newluk[headend:];write(lukrel,newluk)
# A dependency-free local check: the full generated core followed by precisely
# the replacement generic section. The unchanged Tarski bridge needs repo dependencies.
a=newluk.index('namespace SetTheory.BusyBeaver.ZFC.Lukasiewicz');b=newluk.index('end SetTheory.BusyBeaver.ZFC.Lukasiewicz')+len('end SetTheory.BusyBeaver.ZFC.Lukasiewicz')
standalone=core+'\n\n'+newluk[a:b]+'\n\n'
for theorem in ('k','peirce','composition','s'):
 standalone+=f'#print axioms SetTheory.BusyBeaver.ZFC.Lukasiewicz.{theorem}\n'
(out/'SharedImplicationCore.lean').write_text(standalone)
changed={genrel:gen,derrel:der,corerel:core,lukrel:newluk}
patch=''
metrics=[]
for rel,text in changed.items():
 old=(repo/rel).read_text()
 patch+=''.join(difflib.unified_diff(old.splitlines(keepends=True),text.splitlines(keepends=True),fromfile='a/'+str(rel),tofile='b/'+str(rel)))
 metrics.append({'path':str(rel),'old_lines':len(old.splitlines()),'new_lines':len(text.splitlines()),'old_bytes':len(old.encode()),'new_bytes':len(text.encode()),'old_sha256':hashlib.sha256(old.encode()).hexdigest(),'new_sha256':hashlib.sha256(text.encode()).hexdigest()})
(out/'shared-implication.patch').write_text(patch)
(out/'metrics.json').write_text(json.dumps({'pinned_commit':'2ca3a5c16f0876d2cab842056353c03a1ed2f5f0','files':metrics,'old_core_mp_steps':58,'new_core_mp_steps':63,'removed_old_cd_helpers':107,'note':'Old cd_0 was the row leaf, so the 107 removed helpers contained 106 MP steps. Net MP-step reduction: 101.'},indent=2)+'\n')
print(json.dumps(metrics,indent=2))
