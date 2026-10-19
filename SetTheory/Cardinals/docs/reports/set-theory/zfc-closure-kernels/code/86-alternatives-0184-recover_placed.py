import subprocess,json,pathlib
repo='research_sub246/source';base='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/'
for batch, sources in [(162,[63]),(163,[64,65,66,67])]:
 p=json.loads(subprocess.check_output(['git','-C',repo,'show','HEAD:'+base+f'data/intake-{batch}-placement.json']))
 for e in p['placements']:
  if e['local_source'] not in sources:continue
  o=pathlib.Path('research_sub246/context_folds/recovered')/str(e['local_source'])/e['delivered'];o.parent.mkdir(parents=True,exist_ok=True)
  o.write_bytes(subprocess.check_output(['git','-C',repo,'show','HEAD:'+e['target']]))
 print(batch,'done')
