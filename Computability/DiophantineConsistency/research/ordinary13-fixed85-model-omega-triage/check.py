from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-fixed85-model-omega-triage')
P=Path('research/ordinary13-fixed85-source-selection-plan/selection.json')
selection=json.loads(P.read_text());nodes=selection['selected_modules']
# Individually inspected sites: reason identifies the type of the arithmetic
# subgoal, not every variable occurring in the surrounding theorem.
targets={
'DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011':([114],'standard natural beta positivity'),
'DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011':([76],'standard natural beta positivity'),
'DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011':([194],'standard natural beta positivity'),
'DiophantineConsistency.ArithmeticAdaptivePowerLowerBound2011':([22],'standard natural beta lower bound'),
'DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011':([68],'standard natural beta positivity'),
'DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011':([176],'standard natural beta positivity'),
'DiophantineConsistency.ArithmeticAdaptiveTransport2011':([106],'standard natural beta positivity'),
'DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011':([80],'standard natural beta positivity'),
'DiophantineConsistency.ArithmeticAdaptiveRankWindow2011':([136,144,147,157,165,171,172,175,176,181],'standard natural radix, support, digit and beta bounds'),
'DiophantineConsistency.ModelArithmetic':([44,45,61],'standard natural residue witnesses and their bounds'),
'DiophantineConsistency.ArithmeticExpression':([42,51,113,116],'standard natural binary-index and finite-support bounds'),
'DiophantineConsistency.ArithmeticRepresentation':([123,126,139,142,175],'standard natural expression assignments and quotients'),
'DiophantineConsistency.ArithmeticRunTrace':([130,135],'standard finite table indices extracted via standard_of_lt'),
'DiophantineConsistency.ArithmeticWangTable':([351],'standard finite table indices extracted via standard_of_lt'),
'DiophantineConsistency.StrictSigmaOneInduction':([120,121,122,264,276,388,390,391],'syntactic hierarchy levels and Fin arity obligations, not model element inequalities'),
'DiophantineConsistency.FoundationHASigmaOneGG':([205,207],'standard syntactic hierarchy levels'),
'DiophantineConsistency.FoundationPAHFNatSemantics':([45,47],'semantics in the standard natural structure'),
'DiophantineConsistency.IPRAFunctionCongruenceClosed':([44,55],'standard finite variable-index bounds'),
'DiophantineConsistency.PRAWitnessZFCAxioms':([113,114,115,116,117,118],'explicit natural syntax-code constant bounds'),
'DiophantineConsistency.PRABoundedInduction':([63],'standard finite free-variable index bound'),
'DiophantineConsistency.Compact44.CompactWordHorizontalParity':([36],'standard u:ℕ offset bound prior to exact_mod_cast'),
'DiophantineConsistency.Compact44.CompactWordPhysicalFieldParity':([36],'standard u:ℕ offset bound prior to exact_mod_cast'),
'DiophantineConsistency.Compact44.SelectedBandInputs':([30,46],'Fin index or natural position bounds prior to exact_mod_cast'),
'DiophantineConsistency.Compact44.P72Mu':([28],'standard natural exponent comparison'),
'DiophantineConsistency.Compact44.RetainedBetaBytes':([19,40],'standard natural byte-list and predecessor equalities'),
'DiophantineConsistency.Compact44.CompactKernelByteRecipe':([41,42],'standard natural exponent comparison'),
}
records={};total=0
for n,(nums,reason) in targets.items():
 r=nodes[n];p=Path(r['source_path']);raw=p.read_bytes()
 assert sha256(raw).hexdigest()==r['sha256'],n
 lines=raw.decode().splitlines();sites=[]
 for i in nums:
  line=lines[i-1];assert re.search(r'\bomega\b',line),(n,i,line)
  sites.append({'line':i,'text':line.strip()});total+=1
 records[n]={'path':str(p),'sha256':r['sha256'],'reviewed_sites':sites,'classification':reason}
# Anchor the local type explanations to concrete source signatures.
anchors={
 'DiophantineConsistency.ModelArithmetic':['theorem exists_nat_of_lt (r : V) : ∀ n : ℕ','theorem model_residues (n : ℕ)'],
 'DiophantineConsistency.ArithmeticRepresentation':['have hw0 := Nat.zero_le (w 0)'],
 'DiophantineConsistency.ArithmeticRunTrace':['obtain ⟨p, hp, rfl⟩ := standard_of_lt','obtain ⟨β, hβ, rfl⟩ := standard_of_lt'],
 'DiophantineConsistency.ArithmeticWangTable':['obtain ⟨p, hp, rfl⟩ := standard_of_lt','obtain ⟨β, hβ, rfl⟩ := standard_of_lt'],
 'DiophantineConsistency.StrictSigmaOneInduction':['{s n : ℕ}','Fin 2','Rew.castLE (by omega)'],
 'DiophantineConsistency.FoundationPAHFNatSemantics':['∃ d : ℕ'],
 'DiophantineConsistency.PRAWitnessZFCAxioms':['noncomputable def repC : ℕ'],
 'DiophantineConsistency.Compact44.CompactWordHorizontalParity':['(u : ℕ) (hu : u<8)'],
 'DiophantineConsistency.Compact44.CompactWordPhysicalFieldParity':['(u : ℕ) (hu : u<9)'],
 'DiophantineConsistency.Compact44.SelectedBandInputs':['(T : ℕ)','Fin 943','Fin 41'],
 'DiophantineConsistency.Compact44.RetainedBetaBytes':['(a b : ℕ)'],
}
for n,needles in anchors.items():
 text=Path(records[n]['path']).read_text()
 for x in needles:assert x in text,(n,x)
print(json.dumps({'selection_sha256':sha256(P.read_bytes()).hexdigest(),
 'reviewed_module_count':len(records),'reviewed_omega_line_count':total,'records':records,
 'finding':'No additional abstract-model omega hazard identified among the individually inspected sites.',
 'lean_executed':False,'scope':'Source-context triage only; uninspected lexical sites, tactic elaboration, providers, axioms and external frontier remain open.'},sort_keys=True,indent=2))
