#!/usr/bin/env python3
"""Audit the recorded bounded-search counters and portable replay receipts."""
from pathlib import Path
import argparse,csv,hashlib,json,re
ROOT=Path(__file__).resolve().parent

def audit():
 grammar=json.loads((ROOT/'grammar/summary.json').read_text())
 for run in grammar:
  folder=ROOT/'grammar'/run['name']
  log=folder/('order_try1.log'if run['name']=='head_order'else'search.log')
  match=re.findall(r'DONE iterations (\d+) accepted (\d+) hits (\d+) best (\d+) seconds ([0-9.eE+-]+)',log.read_text())
  assert len(match)==1,run['name']
  a,b,c,d,e=match[0]
  assert (int(a),int(b),int(c),int(d))==(run['iterations'],run['accepted'],run['hits'],run['best_reader_score'])
  hits=folder/('order_try1.csv'if run['name']=='head_order'else'hits.csv')
  assert len(list(csv.DictReader(hits.open())))==run['hits']==0
 physical=json.loads((ROOT/'physical/summary.json').read_text())
 for run in physical:
  stem=run['family'];log=(ROOT/'physical'/(stem+'_merge.log')).read_text()
  m=re.findall(r'DONE pairs (\d+) trials (\d+) combos (\d+) hits (\d+) seconds',log)
  assert len(m)==1 and list(map(int,m[0]))==run['counts']
  assert not (ROOT/'physical'/(stem+'_hits.jsonl')).read_text().strip()
 composition=json.loads((ROOT/'composition/replay.json').read_text())
 assert len(composition['results'])==432 and composition['summary']['below_194']==0
 old=[]
 for line in (ROOT/'composition/gd_variants.log').read_text().splitlines():
  m=re.match(r'^(\w+)\s+(\d+)\s+(\d+)\s+(\d+)\s',line)
  if m:old.append((m[1],int(m[2]),int(m[3]),int(m[4])))
 assert old==[(x['name'],x['optimistic_controls'],x['raw_states'],x['matching_size'])for x in composition['results']if x['optimistic_controls']<=194]
 loops=json.loads((ROOT/'loop_sweep/report.json').read_text())
 assert loops==json.loads((ROOT/'loop_sweep/replay.json').read_text()) and len(loops)==40
 provenance=json.loads((ROOT/'INPUT_PROVENANCE.json').read_text())
 for item in provenance['inputs']:
  assert hashlib.sha256((ROOT/item['file']).read_bytes()).hexdigest()==item['sha256'],item['file']
 result={'status':'PASS','grammar_runs':len(grammar),'grammar_mutation_slots':sum(x['iterations']for x in grammar),
         'grammar_accepted_mutations':sum(x['accepted']for x in grammar),'grammar_hits':sum(x['hits']for x in grammar),
         'physical_control_pairs':sum(x['counts'][0]for x in physical),
         'physical_single_row_trials':sum(x['counts'][1]for x in physical),
         'physical_joint_action_pairs':sum(x['counts'][2]for x in physical),
         'physical_hits':sum(x['counts'][3]for x in physical),
         'composition_combinations':len(composition['results']),'composition_log_rows_matched':len(old),
         'corrected_loop_candidates':len(loops),'loop_optimistic_194':sum(x['lower']==194 for x in loops),
         'loop_optimistic_195':sum(x['lower']==195 for x in loops),
         'additional_input_hashes_verified':len(provenance['inputs']),
         'scope':'Audit of archived counters and exact finite replay results; no machine-size lower bound.'}
 assert result['grammar_mutation_slots']==37916566
 assert (result['physical_control_pairs'],result['physical_single_row_trials'],result['physical_joint_action_pairs'])==(56163,70793172,391365)
 return result

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
 a=p.parse_args();result=audit()
 if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
