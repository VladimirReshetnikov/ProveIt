from general_rotations import *
sys.path.insert(0,str(P/'baseline226/vendor/proveit'));import symbolic_runtime as engine
basis=Path(__file__).parent/'dn4_open_rotations'
scan=json.loads((basis/'scan.json').read_text());output=[]
for rp in sorted(basis.glob('layout_*_receipt.json')):
 rec=json.loads(rp.read_text())
 if rec['states']>225:continue
 name=rp.name.replace('_receipt.json','');t,_=v.parse_table((basis/(name+'.tm')).read_bytes());sites=json.loads((basis/(name+'_sites.json')).read_text())
 mp={int(k):z for k,z in json.loads((P/'baseline226/source/legacy_state_map.json').read_text())['k230_to_old'].items()}
 for q,b in t:
  if q>=230:mp[q]=q+300
 mp[254]=254;old={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()}
 r=dict(name=name,rotation=rec['rotation'],states=rec['states'])
 try:
  lemmas,blocks=engine.prove_blocks(old);seen=set()
  for i,s in enumerate(sites):
   for pos in((False,True)if s[1]=='CD'else(False,)):
    key=tuple(s[1:])+(pos,)
    if key in seen:continue
    seen.add(key);engine.case(old,lemmas,s,pos)
  r.update(status='PASS_REPRESENTATIVE_CASES',cases=len(seen))
 except Exception as exc:r.update(status='NOT_PROVED',site_index=i,site=s,positive=pos,reason=repr(exc))
 print(json.dumps(r),flush=True);output.append(r)
c.dump(basis/'representative_probes.json',output)
