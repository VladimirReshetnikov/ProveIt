from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
A=Path('research_sub214d/intake/ZFC_Conditional_Marker_215_2026-10-21/ZFC_Conditional_Marker_215_2026-10-21')
paths={
 'K215':(A/'reference/primary215/k215.native.tm','9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'),
 'CM215':(A/'machine/marker215.native.tm','e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252'),
 'ST215':(Path('research_sub214d/repaired_allocation/common215/inputs/st215.native.tm'),'d5237504325eee96b0040d4d9574731a1caf4bcda3d6a49e94827d9532a664e1'),
 'COMMON215':(Path('research_sub214d/repaired_allocation/common215/candidate.native.tm'),'e207c39092984959840e437f18a6c4d649716ae3a6f5ebdc1b243c0dbed00abd')}
meta={}
for name,(path,pin)in paths.items():
 raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()==pin
 (D/'inputs'/f'{name}.native.tm').write_bytes(raw)
 rows={}
 for line in raw.decode().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in rows;rows[q,b]=w,1 if d=='R'else-1,z
 qs=sorted({q for q,b in rows});assert len(qs)==215 and len(rows)==430 and 254 not in qs
 assert all((q,b)in rows for q in qs for b in (0,1)) and {z for w,d,z in rows.values()}-set(qs)=={254}
 ids={q:i for i,q in enumerate(qs)}
 (D/'inputs'/f'{name}.rows').write_text(f'215 {ids[0]}\n'+''.join(f'{ids[q]} {b} {w} {d} {ids.get(z,215)}\n'for(q,b),(w,d,z)in sorted(rows.items())))
 meta[name]={'original_path':str(path),'sha256':pin,'native_labels':qs,'start_native':0,'halt_native':254,'working_states':215,'transition_rows':430}
(D/'inputs.json').write_text(json.dumps(meta,indent=2)+'\n');print('PREPARED',list(meta))
