#!/usr/bin/env python3
"""Pin the exact model-source interfaces used by the unelaborated client."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent
root=here.parents[1]
pins={
'Lean/DiophantineConsistency/ZRows/PellEvenChebyshev.lean':'290124437283244ec2733ab3e423fa64be407e3a97666052c4eeb969117e01d8',
'Lean/DiophantineConsistency/ArithmeticPellPeriodicity.lean':'93e8e34ae100735ca214cc4039c978b1cdefffffccdb38f7626547a405b0e5bb',
'Lean/DiophantineConsistency/ArithmeticPellResidueClasses.lean':'42dd190da5e7ab35ce7a15ea0b6c08b6fea02d990e80e4047dceeec200b02088',
'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16',
'Lean/DiophantineConsistency/ArithmeticPellHalfIndex.lean':'7703193660d8ae98408d1ec3a83f6f8811927252e739bb7af18dbafb833a8877',
}
def readpin(p,h):
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s={p:readpin(p,h) for p,h in pins.items()}
e=s['Lean/DiophantineConsistency/ZRows/PellEvenChebyshev.lean']
sign=e[e.index('theorem sign_index'):e.index('/-- **Even ordinates**')]
assert 'ycoord (2*t+1) b%(2*(b+3))=(2*t+1)%(2*(b+3))' in sign
assert 'induction t using ISigma1.sigma1_succ_induction' in sign
assert '· definability' in sign
p=s['Lean/DiophantineConsistency/ArithmeticPellPeriodicity.lean']
assert 'ycoord (2*time) b=2*xcoord time b*ycoord time b' in p
r=s['Lean/DiophantineConsistency/ArithmeticPellResidueClasses.lean']
assert '(a%n)%m=a%m := ArithmeticModularCancellation.mod_mod_of_dvd hm hdiv a' in r
rec=s['Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean']
assert 'instance y_definable : 𝚺₁-Function₂[V] ycoord' in rec
b=(here/'PellOrdinateParity.lean.src').read_bytes(); draft=b.decode()
assert 'theorem ordinate_mod_two (n b : V) : ycoord n b % 2 = n % 2' in draft
assert 'even_or_odd n' in draft and '(sign_index b t).2' in draft
assert 'sorry' not in draft and '\naxiom ' not in draft
print(json.dumps({'source_sha256':pins,'draft_sha256':hashlib.sha256(b).hexdigest(),'odd_index_induction_interface_pinned':True,'ycoord_sigma1_function_interface_pinned':True,'scope':'lexical source-interface check only; no Lean elaboration, model proof certification, graph transport or iPRA endpoint','lean_elaborated':False},sort_keys=True,indent=2))
