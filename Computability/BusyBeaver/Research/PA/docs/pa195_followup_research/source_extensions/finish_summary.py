from pathlib import Path
import json,shutil
P=Path(__file__).resolve().parent
# This script only reads the portable, completed run receipts.
paths=[('Head roles and order','head_search/run2.json'),('Forced head changes','head_search/forced1.json'),('Gamma parameter','gamma_search/run1.json'),('48 gate forms','gate_search/run1.json'),('Witness bundle','bundle_search/run1.json')]
rows=[]
for title,file in paths:
 r=json.loads((P/'search'/file).read_text())
 rows.append({'family':title,'receipt':'search/'+file,**r})
summary={'completed_runs':len(rows),'scored_evaluations':sum(r['evaluations']for r in rows),'stochastic_proposal_slots':sum(r['stochastic_attempts']for r in rows),'fixed_association_assignments':rows[0]['direct_assignments'],'sub195_scored_candidates':sum(r['sub195_scores']for r in rows),'runs':rows,'scope':'Finite heuristic search. Score above 64 can be an optimistic matching bound; all potential scores below 61 use exact local fold-compatibility checks. No physical sub-195 table or global lower bound is established.'}
(P/'search_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=[r'\subsection{Finite searches of the new source families}',r'The five completed runs used '+format(summary['fixed_association_assignments'],',')+r' fixed-association assignments and '+format(summary['stochastic_proposal_slots'],',')+r' stochastic proposal slots. Together they made '+format(summary['scored_evaluations'],',')+r' grammar-scoring calls. No score below 61 was found.',r'\begin{center}',r'\small',r'\begin{tabular}{lrrr}',r'\toprule',r'Family & Scored evaluations & Best score & Scores below 61\\',r'\midrule']
for r in rows:
 score='61 / 65'if 'best'in r else str(r['best_changed'])
 lines.append(r['family']+' & '+format(r['evaluations'],',')+' & '+score+' & '+str(r['sub195_scores'])+r'\\')
lines +=[r'\bottomrule',r'\end{tabular}',r'\end{center}',r'The first row distinguishes the unchanged PA195 seed (61) from changed words (65). It exhausts 373,248 head-role choices and 720 head orders at fixed association before its bounded walk. The next run forces changed-word restarts. The last three runs respectively use 240, 480, and 240 restarts of 10,000 proposal slots.',r'The inherited fixed part has 134 controls. An admissible effective reader score of 61 corresponds to the existing 195-state allocation. The scorer checks geometry first, uses matching as an optimistic bound, and performs exact simultaneous local fold-choice checking whenever that bound is at most 64. Scores above 64 need not be realizable state counts. Even a better locally compatible score would still require the complete physical scanner/runtime and startup checks. The JSON receipts preserve seeds, proposal slots, actual evaluations, acceptances, and elapsed times; standalone C++17 sources and input headers permit replay. These finite searches are not lower bounds.']
(P/'search_summary.tex').write_text('\n'.join(lines)+'\n')
print(json.dumps({k:v for k,v in summary.items()if k!='runs'},indent=2))
