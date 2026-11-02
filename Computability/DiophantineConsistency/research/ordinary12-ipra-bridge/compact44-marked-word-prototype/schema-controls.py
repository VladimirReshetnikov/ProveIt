import importlib.util,json,copy,subprocess
from pathlib import Path
base=Path(__file__).resolve().parents[1]
results=[]
for name,old in [('compact44-marked-word-prototype','9e44ca5cef'),('compact44-inverse-lookup-prototype','b929bbb5c0')]:
 p=base/name/'replay.py'; spec=importlib.util.spec_from_file_location('driver_'+name.replace('-','_'),p);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 x=json.loads((mod.AUDIT/'CHECK.json').read_text());obs=json.loads((mod.AUDIT/'terminal-observation.json').read_text())
 legacy={'__file__':str(p),'__name__':'legacy_driver'}
 old_source=subprocess.run(['git','show',old+':Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/'+name+'/replay.py'],cwd=base,check=True,capture_output=True).stdout
 exec(compile(old_source,old,'exec'),legacy)
 try:legacy['pins']();raise AssertionError('old driver unexpectedly accepted actual observation')
 except ValueError as e:
  if str(e)!='parent audit observation':raise
 mod.pins();assert mod.valid_parent_observation(x,obs)
 n=0
 for key,value in [('independent_parent_rerun_exit',1),('independent_review_exit',1),('check_sha256','0'*64),('lean_launched',True)]:
  for mode in ('missing','wrong'):
   bad=copy.deepcopy(obs)
   if mode=='missing':bad.pop(key)
   else:bad[key]=value
   assert not mod.valid_parent_observation(x,bad),(key,mode)
   n+=1
 for key in ('independent_parent_rerun_exit','independent_review_exit'):
  bad=copy.deepcopy(obs);bad[key]=False;assert not mod.valid_parent_observation(x,bad);n+=1
 for mode in ('missing','wrong'):
  bad=copy.deepcopy(x)
  if mode=='missing':bad.pop('status')
  else:bad['status']='wrong'
  assert not mod.valid_parent_observation(bad,obs);n+=1
 results.append({'driver':name,'old_pins_observed':'rejected actual committed observation','corrected_pins':'accepted actual committed observation','negative_controls':n})
print(json.dumps({'status':'PASS_MATCHING_PARENT_SCHEMA_CONTROLS','lean_launched':False,'results':results},indent=2))
