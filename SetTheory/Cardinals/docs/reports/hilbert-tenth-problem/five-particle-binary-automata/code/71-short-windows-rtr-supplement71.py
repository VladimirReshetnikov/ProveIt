#!/usr/bin/env python3
"""Independent inert-data checks supplementing the presentation/release replay."""
from pathlib import Path
import hashlib
import json
import stat
import zipfile
B=Path('/workspace/shared/report71-independent-release-tools-review-20261004')
C=B/'scratch/release-clone'
E=B/'scratch/extracted'
M=json.loads((C/'RELEASE_MANIFEST.json').read_bytes())
checks={}
for kind in ('files','directories'):
    for name,row in M[kind].items():
        p=E/name
        s=p.lstat()
        assert stat.S_IMODE(s.st_mode)==row['mode'] and s.st_mtime_ns==row['mtime_ns']
        if kind=='files':
            assert stat.S_ISREG(s.st_mode) and s.st_nlink==1
            data=p.read_bytes()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
        else:
            assert stat.S_ISDIR(s.st_mode)
expected=set(M['files'])|set(M['directories'])|{'RELEASE_MANIFEST.json'}
assert {p.relative_to(E).as_posix() for p in E.rglob('*')}==expected
checks['independent_extraction_bytes_modes_nanosecond_mtimes_and_object_set']=True
with zipfile.ZipFile(B/'scratch/archive-a.zip') as z:
    names=['Report71/'+n for n in sorted([*M['files'],'RELEASE_MANIFEST.json'])]
    assert z.namelist()==names and z.testzip() is None
    for info in z.infolist():
        assert info.date_time==(2026,10,4,0,0,0) and info.create_system==3
        assert info.compress_type==zipfile.ZIP_DEFLATED
        assert stat.S_ISREG(info.external_attr>>16)
        assert z.read(info)==(C/info.filename.removeprefix('Report71/')).read_bytes()
checks['independent_archive_order_timestamp_compression_crc_payloads']=True
P=C/'science/proof-packet/evidence'
b=json.loads((P/'before.json').read_bytes()); a=json.loads((P/'after.json').read_bytes())
x=b['separately_observed_live_report70']; y=a['separately_observed_live_report70']
added=sorted(set(y)-set(x)); removed=sorted(set(x)-set(y)); changed=[n for n in set(x)&set(y) if x[n]!=y[n]]
assert len(added)==49 and not removed and changed==['/workspace/shared/report70-two-scale-radius-release-20261004/qa']
assert set(x[changed[0]])==set(y[changed[0]])=={'mode','mtime_ns'}
assert x[changed[0]]['mode']==y[changed[0]]['mode'] and x[changed[0]]['mtime_ns']!=y[changed[0]]['mtime_ns']
assert b['frozen_inputs']==a['frozen_inputs']
A=C/'audits/fresh-independent'
bb=json.loads((A/'before.json').read_bytes()); aa=json.loads((A/'after.json').read_bytes())
assert bb['frozen_inputs']==aa['frozen_inputs'] and bb['live_report70']==aa['live_report70']
checks['historical_existing_entry_change_is_only_qa_mtime']={'path':changed[0],'before':x[changed[0]],'after':y[changed[0]]}
checks['historical_added_entries']=len(added)
checks['later_audit_endpoints_equal']=True
checks['historical_equality_not_continuous_immutability']=True
receipt={'status':'PASS','scientific_programs_executed':False,'checks':checks}
(B/'receipts/SUPPLEMENTAL_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,indent=2,sort_keys=True))
