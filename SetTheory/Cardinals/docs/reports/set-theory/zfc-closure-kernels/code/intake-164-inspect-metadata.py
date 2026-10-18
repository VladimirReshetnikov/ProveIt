"""Reviewer-owned static parser only: no imports or execution of supplied code.
Writes only sibling metadata.json; never steps a Turing machine.
"""
from pathlib import Path
from collections import Counter
import hashlib, json, re
B=Path('/tmp/zfc245-8286787-review/extracted/zfc245-proof-20261018')
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
O=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 d={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '): start=int(line.split()[-1])
  elif line and not line.startswith('#'):
   a,b,c,move,e=line.split();a,b,c,e=map(int,(a,b,c,e))
   assert b in (0,1) and c in (0,1) and move in ('L','R') and (a,b) not in d
   d[a,b]=(c,move,e)
 states={q for q,b in d}
 assert start in states and set(d)=={(q,b) for q in states for b in (0,1)}
 return start,d,states
nstart,new,ns=table(B/'machine/zfc245_old.tm')
cstart,canon,cs=table(B/'machine/zfc245.tm')
bstart,base,bs=table(B/'reference/context246/machine/zfc_prefix246_old.tm')
mstart,maint,ms=table(R/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246_old.tm')
assert (bstart,base)==(mstart,maint)
ren=json.loads((B/'machine/renumbering.json').read_text());mp={int(k):v for k,v in ren['old_to_canonical'].items()}
assert len(set(mp.values()))==246 and {(mp[q],b):(w,d,mp[t]) for (q,b),(w,d,t) in new.items()}==canon
assert cs==set(range(245)) and set(t for w,d,t in canon.values())-cs=={245}
assert (nstart,cstart,mp[95],mp[96],mp[254])==(95,0,0,88,245)
gram=json.loads((B/'grammar.json').read_text()); rules={w:(a,b) for w,a,b in gram['rules']}
allocation=json.loads((B/'certificate/allocation.json').read_text())
source=json.loads((B/'inputs/closed-sequence-grammar-next22.json').read_text())
symbols=json.loads((B/'inputs/semantic-symbols.json').read_text());enc={v:k for k,v in symbols.items()}
words={int(q):''.join(enc[c] for c in word) for q,word in source['flattened_semantic_words'].items()}
sequences=set(source['sequence_states']); fixed=bs-sequences-{74,177}
assert len(rules)==len(allocation)==len(set(allocation.values()))==128
assert set(allocation)==set(rules) and set(allocation.values()).isdisjoint(fixed)
assert set(allocation.values())|fixed==ns
assert all(w==a+b and a and b for w,(a,b) in rules.items())
def dst(w): return source['atoms'][symbols[w]]['state'] if len(w)==1 else allocation[w]
for w,(l,r) in rules.items():
 assert new[allocation[w],0]==(0,'R',dst(l))
 assert new[allocation[w],1]==(1,'R',dst(r))
routes={(x['source'],x['read']):x['word'] for x in gram['routes']}
for q in fixed:
 for bit in (0,1):
  w,d,t=base[q,bit]
  expected=(0,'L',84) if (q,bit)==(58,0) else (w,d,allocation[routes[q,bit]]) if (q,bit) in routes else (w,d,allocation[words[t]]) if t in sequences else (w,d,t)
  assert new[q,bit]==expected
# Word parse identity from semantic input uses split positions; no supplied code.
sem=(B/'inputs/semantic.txt').read_text().splitlines();num,nroots,natoms=map(int,sem[0].split())
oldrules={}
for line in sem[1:num+1]:
 split,w,q=line.split();split=int(split);oldrules[w]=(w[:split],w[split:])
retained=set(oldrules)&set(rules)
fixedchanges=[{'state':q,'read':b,'before':base[q,b],'after':new[q,b]} for q in sorted(fixed) for b in (0,1) if base[q,b]!=new[q,b]]
commonchanges=[{'state':q,'read':b,'before':base[q,b],'after':new[q,b]} for q,b in sorted(set(base)&set(new)) if base[q,b]!=new[q,b]]
sites=json.loads((B/'certificate/sites_logical.json').read_text());phys=json.loads((B/'certificate/sites_physical.json').read_text())
PHYS=(6,2,0,4,3,7,8,5,1)
assert phys==[[p,op,PHYS[r] if op in ('CI','CD') else r] for p,op,r in sites]
# Decode only the literal maintained Lean tree expression; no Lean execution.
act=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ActualTree254.lean'
txt=act.read_text().split('def tree : Tree :=',1)[1].split('theorem tree_eq',1)[0]
toks=re.findall(r'\.(?:node|leaf|decnz|inc|brk|cont|halt)\b|\d+',txt)
i=0;oldsites=[]
ops={'.decnz':'CD','.inc':'CI','.brk':'CB','.cont':'CC','.halt':'CH'}
def parse(p=''):
 global i
 tag=toks[i];i+=1
 if tag=='.node':parse(p+'0');parse(p+'1')
 else:
  assert tag=='.leaf';op=toks[i];i+=1
  r=None if op=='.halt' else int(toks[i]);i+=int(op!='.halt')
  oldsites.append([p,ops[op],r])
parse();assert i==len(toks)
assert [x[1:] for x in sites]==[x[1:] for x in oldsites]
# Compare source grammar AST to maintained full ordered tree, including old paths.
dag=source['ast_dag'];dag_sites=[]
def walk(n,p=''):
 row=dag[n]
 if row[0]=='N':walk(row[1],p+'0');walk(row[2],p+'1')
 else:
  op,*arg=row[1];dag_sites.append([p,{'inc':'CI','dec':'CD','brk':'CB','cont':'CC','halt':'CH'}[op],arg[0] if arg else None])
walk(source['original_ast']);assert dag_sites==oldsites
leaves={p for p,_,_ in sites};prefixes={p[:i] for p in leaves for i in range(len(p))}
assert len(leaves)==len(sites)==6460 and not leaves&prefixes
assert all(p+c in leaves|prefixes for p in prefixes for c in '01')
# Static final bootstrap frame equality only, no replay of either trace.
boot=json.loads((B/'certificate/blank_boot.json').read_text());baseboot=json.loads((B/'reference/context246/results/bootstrap.json').read_text())['old_labels']
assert boot['all_one_positions']==baseboot['all_one_positions']
assert boot['spare_values']==[1]*167 and boot['logical_registers']==[3,0,0,0,3,0,0,0,0]
assert boot['blank_steps']==407915
bisim=json.loads((B/'certificate/register_bisimulation.json').read_text())
entries=bisim['entries'];edges=[x for row in entries for x in row[2:] if x is not None]
assert all(type(x) is int and 0<=x<len(entries) for x in edges)
# This only inventories the supplied certificates, not checking their runtime proofs.
records=[]
for name in ['certificate/machine-audit.json','certificate/local-routing-audit.json','certificate/full-symbolic-all-values.json','certificate/full-symbolic-summary.json','results/delivery/frame-composition.json','results/independent/frame245-composition-check.json']:
 p=B/name;x=json.loads(p.read_text());records.append({'path':name,'sha256':sha(p),'status':x.get('status'),'table_sha256':x.get('table_sha256',x.get('old_label_sha256')),'canonical_sha256':x.get('canonical_sha256'),'alternative_sites_sha256':x.get('alternative_sites_sha256'),'counts':x.get('counts'),'complete':x.get('complete'),'frame_padding':x.get('frame_padding'),'minimum_steps':x.get('minimum_steps')})
# Inspect exact parameterization transforms without importing their checker.
a=(B/'reference/context246/sources/prior/prefix_affine.py').read_text();p=(B/'code/parametric_prefix_affine.py').read_text()
expected=a.replace('from collections import Counter\n','from collections import Counter\n\n# Parameterized frame width; all symbolic inference rules below are unchanged.\n# Source: inherited context246/sources/prior/prefix_affine.py.\nPADDING = 40\n').replace('40-len(pc)','PADDING-len(pc)').replace("    q='96';onleft=False;left=[('b',1)]","    assert type(PADDING) is int and PADDING >= len(pc)\n    q='96';onleft=False;left=[('b',1)]")
assert p==expected
full=(B/'reference/full_symbolic_original.py').read_text()
expected=full.replace('ROOT = Path(__file__).resolve().parents[1]','ROOT = Path(__file__).resolve().parents[1]\n# Only the uniform source/target frame padding and its input guard differ.\nPADDING = 64').replace("BASE = ROOT / 'reference/context246'","BASE = ROOT / 'reference/context246'\nsys.path.insert(0,str(ROOT/'code'))").replace('40-len(pc)','PADDING-len(pc)').replace('40+extra+int(overflow)-len(successor)','PADDING+extra+int(overflow)-len(successor)').replace('len(p)<=34','len(p)<=PADDING').replace("out=dict(status='PASS' if complete else 'PASS_LIMITED',","out=dict(frame_padding=PADDING,status='PASS' if complete else 'PASS_LIMITED',")
assert (B/'code/full_symbolic_parametric.py').read_text()==expected
orig=(B/'reference/context246/code/review_affine_source.py').read_text();start=orig.index('def check_sites(');end=orig.index('\n\n',orig.index('max_rules=max_rules, rule_counts=dict(rule_counts))',start));f=orig[start:end]
f=f.replace('def check_sites(affine, table, sites):','def check_sites(affine, table, sites, padding):\n    assert type(padding) is int and padding >= max(len(p) for p,op,r in sites)\n    assert affine.PADDING == padding').replace('<= 40','<= padding').replace('constant_gap = 40 +','constant_gap = padding +').replace('return dict(cases=full_path_cases,','return dict(padding=padding, cases=full_path_cases,')
assert (B/'code/parametric_affine_driver.py').read_text().split('def check_sites(',1)[1]==f.split('def check_sites(',1)[1]+'\n'
files=['machine/zfc245.tm','machine/zfc245_old.tm','machine/renumbering.json','grammar.json','certificate/allocation.json','certificate/sites_logical.json','certificate/sites_physical.json','certificate/register_bisimulation.json','certificate/blank_boot.json','reference/context246/machine/zfc_prefix246.tm','reference/context246/machine/zfc_prefix246_old.tm','code/build_routing_machine.py','code/audit_routing_grammar.py','code/check_parameterization.py','code/parametric_affine_driver.py','code/parametric_prefix_affine.py','code/full_symbolic_parametric.py','code/audit_existing_machine.py','code/verify.py','code/verify_all.py','code/verify_machine_frame245.py','code/state_reduction/check_short_scan_boot.py','code/state_reduction/check_candidate_boot.py','reference/context246/code/check_macro_inductions.py','inputs/closed-sequence-grammar-next22.json','inputs/state_reduction/bootstrap-lock54.txt','report.tex','README.md','proof/routing_bootstrap_lemma.tex']
pins=[{'path':n,'sha256':sha(B/n),'bytes':(B/n).stat().st_size} for n in files]
pairs=[]
for a,b in [('machine/zfc245.tm','certificate/machine.tm'),('machine/zfc245_old.tm','certificate/machine_old.tm'),('machine/renumbering.json','certificate/renumbering.json'),('reference/context246/machine/zfc_prefix246_old.tm','reference/tables/zfc_prefix246_old.tm'),('reference/context246/results/bootstrap.json','reference/bootstrap/bootstrap.json'),('reference/context246/sources/Prog254.v','reference/source/Prog254.v')]:
 pairs.append({'left':a,'right':b,'byte_identical':(B/a).read_bytes()==(B/b).read_bytes()})
result={'scope':'Reviewer-owned static parsing and byte comparisons only; no supplied-code import/execution, transition simulation, symbolic proof replay, compiler, version query, or checksum-manifest validation.', 'machine':{'working_states':len(ns),'rows':len(new),'canonical_states':len(cs),'start_old':nstart,'start_canonical':cstart,'dispatch_canonical':mp[96],'halt_canonical':mp[254],'renumbering_exact':True,'baseline_matches_maintained246_transition_for_transition':True,'baseline_old_bytes_equal_maintained':(B/'reference/context246/machine/zfc_prefix246_old.tm').read_bytes()==(R/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246_old.tm').read_bytes(),'removed_numeric_labels':sorted(bs-ns),'added_numeric_labels':sorted(ns-bs),'changed_common_rows':len(commonchanges),'changed_framework_rows':fixedchanges,'full_changed_common_rows':commonchanges},'allocation':{'original_grammar_roles':len(sequences),'original_fixed_roles':len(bs-sequences),'new_grammar_roles':len(rules),'retained_fixed_roles':len(fixed),'freed_fixed_roles_reused_in_grammar':[q for q in [74,177] if q in allocation.values()],'literal_allocation_matches_all_490_rows':True,'original_word_count':len(oldrules),'retained_words':len(retained),'absent_old_words':len(set(oldrules)-set(rules)),'new_words':len(set(rules)-set(oldrules)),'retained_parse_unchanged':sum(oldrules[w]==rules[w] for w in retained),'retained_parse_changed':sum(oldrules[w]!=rules[w] for w in retained),'grammar_declared_framework_before_short_scan':gram['framework_states'],'actual_short_scan_argument_required':not gram.get('short_scan',False)},'source':{'leaves':len(sites),'internal_tree_nodes':len(prefixes),'all_ordered_operations_and_arguments_match_current_ActualTree254':True,'grammar_original_ast_matches_current_tree_with_full_old_paths':True,'changed_leaf_addresses':sum(a[0]!=b[0] for a,b in zip(oldsites,sites)),'maximum_depth':max(len(p) for p,_,_ in sites),'maximum_zero_run':max(len(z) for p,_,_ in sites for z in p.split('1')),'operation_counts':dict(Counter(op for p,op,r in sites)),'guard_count':sum(2 if op=='CD' else 1 for p,op,r in sites),'physical_mapping_exact':True,'bisimulation_pairs_metadata_only':len(entries),'bisimulation_edges_metadata_only':len(edges),'bisimulation_halt_pairs_metadata_only':sum(row[2:] == [None,None] for row in entries)},'bootstrap':{'old_claimed_steps':410735,'new_claimed_steps':boot['blank_steps'],'difference':410735-boot['blank_steps'],'all_351_recorded_one_positions_equal_baseline':True,'same_logical_seed':boot['logical_registers'],'spare_count':len(boot['spare_values']),'new_frame_padding':64,'initial_header_distance':boot['header_distance'],'initial_affine_parameter':boot['header_distance']-64,'no_trace_replayed':True},'parameterization_three_exact_transforms_match':True,'duplicate_pairs':pairs,'records_metadata_only':records,'source_pins':pins,'maintained_comparators':[{'path':str(act),'sha256':sha(act)},{'path':str(R/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246_old.tm'),'sha256':sha(R/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246_old.tm')} ]}
(O/'metadata.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'output':str(O/'metadata.json'),'sha256':sha(O/'metadata.json'),'machine_summary':{k:v for k,v in result['machine'].items() if k not in ('full_changed_common_rows','changed_framework_rows')},'allocation':result['allocation'],'source':result['source'],'parameterization':True},indent=2))
