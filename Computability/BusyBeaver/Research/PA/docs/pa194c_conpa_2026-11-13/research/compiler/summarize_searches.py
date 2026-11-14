from pathlib import Path
import json,re
HERE=Path(__file__).resolve().parent
jobs=[('identity1',600,111320263,'Identity source word; reassociation and seven or more compatible folds'),('joint1',480,111320264,'Reassociation with independent parameter permutations in six axiom heads'),('order1',300,111320268,'Reassociation and randomly reordered independent axiom heads'),('scanner1',400,111320269,'Stricter AX scanner bounds m<=5 and mi<=4; effective target60 with one fixed scanner state deleted'),('triple1',480,111320266,'Mixed pool containing original word and incT^3 -> incT^4;decT variants; interrupted'),('triple2',480,111320267,'Nontrivial incT^3 -> incT^4;decT variants only; interrupted')]
result=[]
for name,budget,seed,family in jobs:
 text=(HERE/(name+'.log')).read_text()
 done=re.findall(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([\d.]+)',text)
 cycles=re.findall(r'CYCLE (\d+) best (\d+) now (\d+) pool (\d+) iterations (\d+) nodes (\d+) seconds ([\d.]+)',text)
 improvements=re.findall(r'BEST score (\d+) eff (\d+) nodes (\d+) folds (\d+) pen (\d+) iteration (\d+) seconds ([\d.]+)',text)
 row={'name':name,'planned_seconds':budget,'seed':seed,'family':family,'complete':bool(done)}
 if done:
  it,accepted,hits,best,seconds=done[-1];row.update(iterations=int(it),accepted=int(accepted),hits=int(hits),best_score=int(best),elapsed_seconds=float(seconds))
 elif cycles:
  cycle,best,now,pool,it,nodes,seconds=cycles[-1];row.update(last_recorded_iteration=int(it),best_score=int(best),last_recorded_seconds=float(seconds),final_iteration_count_unknown=True)
 row['improvements']=[dict(score=int(a),effective_readers=int(b),raw_readers=int(c),folds=int(d),penalty=int(e),iteration=int(f),seconds=float(g)) for a,b,c,d,e,f,g in improvements]
 result.append(row)
receipt={'target':'Fewer than 194 working states','fixed_controls':134,'runs':result,'pure_js_fallback':json.loads((HERE/'pure_js_receipt.json').read_text()),'negative_results_are_not_lower_bounds':True,'physical_validation_scope':'No new machine from these search families is claimed. Candidate scores are filters, not end-to-end correctness proofs.'}
(HERE/'search_summary.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
