from pathlib import Path
import sys,json,time
import direct_screen as D
sys.path.insert(0,str(D.D.parent/'k223_merged_runtime_audit/runtime'));import symbolic_runtime as S
p=D.D/'shared_cancellation/candidate.native.tm';T0=S.r.table(p);mp={int(q):v for q,v in json.load(open(D.D/'NATIVE_TO_LEGACY.json')).items()}
for q in {q for q,b in T0}|{254}:
 if q not in mp:mp[q]=q+1000
T={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T0.items()};ss=json.load(open(D.D.parent/'research218_source/shared_cancellation_sites.json'));L,blocks=S.prove_blocks(T)
ci=[(i,s,False)for i,s in enumerate(ss)if s[1:]==['CI',6]and s[0].endswith('1')];cb=[(i,s,False)for i,s in enumerate(ss)if s[1]=='CB'and s[0].endswith('1111')];dc=[]
for reg in(5,6):
 i,s=next((i,s)for i,s in enumerate(ss)if s[1:]==['CD',reg]and i>4500)
 dc.extend([(i,s,False),(i,s,True)])
cases=[];start=time.monotonic()
for i,s,b in ci+cb+dc:
 try:r=S.case(T,L,s,b);r.pop('trace');r['rows']=sorted(r['rows']);cases.append(dict(index=i,site=s,positive=b,**r));print('PASS',i,s,b,flush=True)
 except Exception as e:cases.append(dict(index=i,site=s,positive=b,error=repr(e)));print('FAIL',i,s,b,repr(e),flush=True);break
D.dump('SHARED_SYMBOLIC_PILOT.json',dict(cases=cases,count=len(cases),requested=len(ci+cb+dc),seconds=time.monotonic()-start,table_sha256=D.H(p.read_bytes()),scope='Targeted arbitrary-natural whole-frame cases only; not full runtime'))
