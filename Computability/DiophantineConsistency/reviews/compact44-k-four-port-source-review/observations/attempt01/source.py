#!/usr/bin/env python3
"""Read-only independent source, object and retained-K arithmetic audit."""
from pathlib import Path
from hashlib import sha256
import ast
import gzip
import json
import os
import re
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke with python3 -I -S -B')
HERE=Path(__file__).resolve().parent
DC=HERE.parents[1]
ROOT=DC.parents[1]
B=DC/'research/ordinary12-ipra-bridge'
K=B/'compact44-k-byte-recipe-prototype'
TUPLE=B/'compact44-four-port-byte-assembly2'
PRIOR=B/'compact44-four-port-byte-assembly-prototype'
SUFFIXES=('.olean.private.hash','.olean.server.hash','.olean.hash','.olean.private',
          '.olean.server','.olean','.ir.hash','.ir','.ilean.hash','.ilean')
def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
    if not ok: raise RuntimeError(msg)
def record(p):
    p=Path(p)
    if not os.path.lexists(p):return None
    need(p.is_file(),f'dangling/nonfile {p}')
    return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}
def family(n):return next((str(n)[:-len(s)] for s in SUFFIXES if str(n).endswith(s)),None)
def inventory(roots):
    return {str(p):record(p) for root in roots for p in root.rglob('*') if p.is_file() and family(p.name)}
def selected(m):
    lib=Path(m['project'])/'lib'
    live={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
    expected=m['files']
    need(set(live)==set(expected),'selected file set differs: '+str(lib))
    need(all(live[k]['sha256']==expected[k]['sha256'] and live[k]['resolved']==expected[k]['resolved'] for k in live),'selected bytes/targets differ: '+str(lib))
    return live
def guards(r):
    need(r['guards_unchanged'] and all(record(p)==v for p,v in r['guards_before'].items()),'direct/companion guard drift')
def producer(directory,attempt,module,source_pin,object_pin):
    packet=B/directory; obs=packet/'observations'/attempt
    receipt_path=obs/'terminal.json';r=json.loads(receipt_path.read_text())
    source=packet/(module+'.lean');logged_source=obs/'source.lean';log=obs/'compile.log'
    need(r['exit_code']==0 and digest(source)==digest(logged_source)==r['source_sha256']==r['workspace_source_sha256_after']==source_pin,'producer source/receipt: '+module)
    need(digest(log)==r['log_sha256'] and not (obs/'deps.stderr').read_bytes(),'producer log/deps: '+module)
    messages=log.read_text()
    need(not any(word in messages for word in ('error:','warning:','sorryAx')),'producer diagnostic: '+module)
    obj=Path(r['command'][-1]);need(obj.name==module+'.olean' and digest(obj)==r['object_sha256']==object_pin,'producer object: '+module)
    guards(r)
    return {'module':module,'receipt_sha256':digest(receipt_path),'source_sha256':source_pin,
            'object_sha256':object_pin,'object':str(obj),'guard_count':len(r['guards_before'])}

producers=[
 ('compact44-retained-beta-byte-prototype','attempt03','RetainedBetaBytes','843341bb3fde311235b893a35245c3cbc7d7ae5c869fefd6aece51262b26757c','bd1611b2a0a3343d204c558628514b0e7132921a4263429c27b1f296ee03585b'),
 ('compact44-k-byte-recipe-prototype','attempt01','CompactKernelByteRecipe','eb9c2d879a9a8dcd304da80a402d52a4d92bdfcb18c247e54e887914c8528e4b','8982509922de9594e9cca21a873efacb9944d0969a20f7d8e104c305c9f8ae19'),
 ('compact44-low-byte-assembly-attempt2','attempt01','CompactLowByteAssembly','67699cc0e1f832a20f48efd13ed9f535bbddcf2c6d1817edfe74577f5a9a4d05','83bf7396f168ed2a4aa49e0e13ec43a7d265f951e26d7c894b66351002e9d098'),
 ('compact44-mf-byte-assembly-prototype','attempt01','CompactShiftedHighByteAssembly','420ac9903e344d5952a22433003e7b5623514e52c042e017eb924e2f9f8390c2','992dd20b27f39d9fda165349221ca1e93ed36789816d48d17555bea74efec77e'),
 ('generic-four-byte-port-prototype','attempt02','GenericFourBytePorts','82f3c7bf35d31b995bd95ab59ec192ad481532f9f11c127ef9fc3007e3a4c78d','c4cf66185b18c427a3a95ea1be7f2d093456a8bd5eeec58473fde82be4a9abd2'),
 ('compact44-four-port-byte-assembly2','attempt01','CompactFourPortByteAssembly2','597a60517cd5563b21c96077cbead4e5f213ae8a01feac65099fd1512f4dc65a','0f921668ce8407f4a28346a85e2023d131fc4421e00c790048ac2d813f8e3a85')]
prod=[producer(*row) for row in producers]

kprep=K/'observations/prepare-attempt01/manifest.json'; km=json.loads(kprep.read_text())
kr=json.loads((K/'observations/attempt01/terminal.json').read_text())
need(digest(kprep)==kr['manifest_sha256']=='5a91a831350a782f68c8d53ad3e3cb3a828472be6a2eab549293e3b9b6f16427','K manifest pin')
need(km['unchanged'] and not km['suppressed_companions'] and len(km['roots'])==5 and len(km['files'])==361,'K manifest scope')
kroots=[Path(p) for p in km['roots']]
before_k=inventory(kroots)
need(before_k==km['providers_before'],'K root inventory drift')
kseen={};koverlaps=0
for root in kroots:
    for p in root.rglob('*'):
        if not p.is_file() or family(p.name) is None: continue
        rel=p.relative_to(root).as_posix();rec=before_k[str(p)]
        if rel in kseen:
            koverlaps+=1;need(kseen[rel]['sha256']==rec['sha256'],'K root overlap conflict: '+rel)
        else:kseen[rel]=rec
klive=selected(km)
need(set(klive)==set(kseen) and all(klive[x]['sha256']==kseen[x]['sha256'] for x in klive),'K union differs from roots')
need(kr['selected_unchanged'] and kr['providers_unchanged'],'K author pre/post flag')

prior_path=PRIOR/'observations/prepare-attempt01/manifest.json'; prior=json.loads(prior_path.read_text())
tprep=TUPLE/'observations/prepare-attempt01/manifest.json'; tm=json.loads(tprep.read_text())
tr=json.loads((TUPLE/'observations/attempt01/terminal.json').read_text())
need(digest(prior_path)==tm['prior_union_sha256']=='ec3f5afc67e4424d9bd026edf0c4a7e5c8a3cb8817bdc29875e81e3ccfe176c8','prior tuple union pin')
need(digest(tprep)==tr['manifest_sha256']=='14edb04f5ec3bf572cf8a1cf07c35a80d0ac0b5726c3e4affac6797d57d82c42','tuple manifest pin')
need(tm['unchanged'] and not tm['suppressed_companions'] and len(tm['files'])==631 and
     tr['selected_unchanged'] and tr['producers_unchanged'],'tuple author flags')
need(all(record(p)==v for p,v in prior['guards_before'].items()) and
     all(record(p)==v for p,v in tm['guards_before'].items()),'union prior direct guard drift')
need(selected(prior) and selected(tm),'selected tuple union unavailable')
producer_receipts={x['module']:x for x in prod}
for name,module in [('beta','RetainedBetaBytes'),('K','CompactKernelByteRecipe'),('MC','CompactLowByteAssembly'),('MF','CompactShiftedHighByteAssembly')]:
    need(prior['prior_receipt_sha256'][name]==producer_receipts[module]['receipt_sha256'],'producer receipt pin: '+name)
    need(prior['files'][module+'.olean']['sha256']==producer_receipts[module]['object_sha256'],'producer selected hash: '+name)
need(tm['generic_receipt_sha256']==producer_receipts['GenericFourBytePorts']['receipt_sha256'] and
     tm['files']['GenericFourBytePorts.olean']['sha256']==producer_receipts['GenericFourBytePorts']['object_sha256'],'generic selected receipt')

# Independently compare each underlying selected manifest, all live provider
# records, every pairwise shared name, and the resulting selected family set.
prior_maps={}; prior_provider_records={}
for name,entry in prior['prior_manifests'].items():
    p=Path(entry['path']);need(digest(p)==entry['sha256'],'underlying manifest drift: '+name)
    m=json.loads(p.read_text());need(m['unchanged'] and not m['suppressed_companions'],'underlying manifest flags: '+name)
    need(m['providers_before']==entry['providers_before'],'underlying provider records: '+name)
    need(all(record(path)==rec for path,rec in m['providers_before'].items()),'underlying provider path drift: '+name)
    prior_provider_records[name]=m['providers_before']; prior_maps[name]=selected(m)
need(set(prior_maps)=={'K','MC','MF'},'unexpected underlying manifests')
pairwise={}
for left,right in [('K','MC'),('K','MF'),('MC','MF')]:
    common=set(prior_maps[left])&set(prior_maps[right])
    need(all(prior_maps[left][x]['sha256']==prior_maps[right][x]['sha256'] for x in common),'shared file hash conflict: '+left+'/'+right)
    pairwise[left+'/'+right]=len(common)
expected_names=set().union(*(set(m) for m in prior_maps.values()))
expected_names.update(x['module']+'.olean' for x in prod[:4])
need(set(prior['files'])==expected_names,'four-producer union set mismatch')
need(set(tm['files'])==expected_names|{'GenericFourBytePorts.olean'},'generic tuple union set mismatch')
for name in expected_names:
    candidates=[m[name]['sha256'] for m in prior_maps.values() if name in m]
    candidates += [x['object_sha256'] for x in prod[:4] if name==x['module']+'.olean']
    need(candidates and len(set(candidates))==1 and tm['files'][name]['sha256']==candidates[0], 'union hash mismatch: '+name)

# Check source statements explicitly, including the natural decoder codomain
# and exactly one beta shift in the symbolic fourth port.
ks=(K/'CompactKernelByteRecipe.lean').read_text()
ts=(TUPLE/'CompactFourPortByteAssembly2.lean').read_text()
generic=(B/'generic-four-byte-port-prototype/GenericFourBytePorts.lean').read_text()
ports=(B/'compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean').read_text()
need('def bytes : List ℕ := (List.range 74111).map byteAt' in ks and
     'theorem decode_bytes : Nat.ofDigits 256 bytes = paramKernel CompactSymbolicKernel.rho' in ks and
     'exact bytes_windows' in ks and 'TopDigit.kernel_bounds.2' in ks, 'K statement/assembly mismatch')
need('theorem tuple4 (a b c d : List ℕ) (A B C D : ℕ)' in generic and
     '![Nat.ofDigits 256 a, Nat.ofDigits 256 b,' in generic, 'generic natural decoder mismatch')
need('def bytePorts : Fin 4 → List ℕ :=' in ts and
     '(fun j => Nat.ofDigits 256 (bytePorts j)) =' in ts and
     '![CompactFixedBeta.betaNat, paramKernel rho, lowNat, CompactFixedBeta.betaNat + highNat]' in ts and
     'RetainedBetaBytes.decode_betaBytes CompactKernelByteRecipe.decode_bytes' in ts and
     'CompactLowByteAssembly.decode_bytes CompactShiftedHighByteAssembly.decode_bytes' in ts and
     'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports,'tuple statement/once shift mismatch')

# Independently reconstruct the large K integer by the weighted-power formula,
# not by the author's two-digit local-byte procedure.
paths={
 'rows':B/'compact44-943-table-prototype/Compact943Data.lean',
 'kernel':B/'compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean',
 'param':B/'compact44-symbolic-kernel-param-prototype/CompactSymbolicKernelOpaque.lean',
 'mass':B/'compact44-coefficient-mass-prototype/CompactCoefficientMass.lean',
 'sparse':B/'compact44-sparse-k-family-exploration/ConcreteSparseKernel.lean',
 'window':B/'compact44-symbolic-k-byte-window-exploration/SymbolicKernelBytes.lean',
 'binding':DC/'candidates/free-j-polarized-positive/source/positive/coefficients/BINDING.json',
 'payload':DC/'candidates/free-j-polarized-positive/source/positive/coefficients/payloads/K.bin.gz'}
pins={'rows':'10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
 'kernel':'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',
 'param':'fbef8642de957bb39493607cb67edda418f53332af5a92ee594a2a437241e0b8',
 'mass':'ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e',
 'sparse':'bf6acf6496295962f2be177aa6ae5aa214f3c66cc01da283daa81226172ae4aa',
 'window':'b245515e66a89eba3be43d5edb96197d55c7a5138095c429f21ea920d63761b2',
 'binding':'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01',
 'payload':'b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a'}
before={name:p.read_bytes() for name,p in paths.items()}
need(all(sha256(before[n]).hexdigest()==pins[n] for n in paths),'K source or payload pin drift')
rows_text=before['rows'].decode();begin='-- BEGIN PINNED ORDERED ROWS\n';end='\n-- END PINNED ORDERED ROWS'
need(rows_text.count(begin)==rows_text.count(end)==1,'ordered row markers')
rows=ast.literal_eval('['+rows_text.split(begin,1)[1].split(end,1)[0]+']')
need(len(rows)==943 and all(len(t)==4 and all(type(x) is int and x>=0 for x in t) for t in rows),'row shape')
kernel_text=before['kernel'].decode()
match=re.search(r'^def slots : List ℕ := (\[[0-9,]+\])$',kernel_text,re.M)
need(match is not None,'slot source missing')
slots=ast.literal_eval(match.group(1))
need(len(slots)==41 and len(set(slots))==41 and max(slots)<4393,'copy slots')
mass=before['mass'].decode();param=before['param'].decode();sparse=before['sparse'].decode();window=before['window'].decode()
need('t.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34' in mass and
     '1 + 2^10 * (2^41 - value t)' in mass,'selector source shape')
need('r^30+r^62+r^1100+r^2201' in param and
     '(r^(4393-i.val)+r^(5495-i.val))' in param and
     '(r^(4393-position i)+r^(5495-position i))' in param and
     'r^8807*r^42' in param,'paramKernel source shape')
need('[(30,1),(62,1),(1100,1),(2201,1)]' in sparse and '[(8849,1)]' in sparse and
     '(List.range 8850).map (SparseRadix.coefficientAt kernelTerms)' in window,'radix term source shape')
def selector(t):
    a,b,c,d=t
    v=a+2**8*b+2**17*c+2**25*d+127*2**34
    need(0<v<2**41,'selector value outside checked natural-subtraction range')
    return 1+2**10*(2**41-v)
def power(e):return 1 << (67*e)
total=sum(power(e) for e in (30,62,1100,2201,8849))
for i,row in enumerate(rows): total += selector(row)*(power(4393-i)+power(5495-i))
for i,slot in enumerate(slots): total += 2**(10+i)*(power(4393-slot)+power(5495-slot))
binding=json.loads(before['binding']);meta=binding['ports']['K0']
raw=gzip.decompress(before['payload'])
need(meta['upstream_port']=='K' and sha256(raw).hexdigest()==meta['sha256_raw']==
     'c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e','retained K raw hash')
need(len(raw)==meta['raw_bytes']==74111 and total.bit_length()==meta['bits']==592884 and
     len(raw)==(total.bit_length()+7)//8 and total.to_bytes(74111,'little')==raw,'independent weighted K value/bytes')
# Concrete negative control: altering one row changes the K integer.
row0=rows[0]; altered=(row0[0]+1,*row0[1:])
mutant=total+(selector(altered)-selector(row0))*(power(4393)+power(5495))
need(mutant!=total,'mutated row was not detected')
supp=DC/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients'
need((supp/'BINDING.json').read_bytes()==before['binding'] and
     (supp/'payloads/K.bin.gz').read_bytes()==before['payload'],'restored supplement differs from retained parent')
checker=K/'check_recipe.py';checker_before=checker.read_bytes()
need(sha256(checker_before).hexdigest()=='300f474064afaf8451e8874da8a391acb3bc6222cd57956d036d5b5a054b5ba1','K checker pin')
run=subprocess.run([sys.executable,'-I','-S','-B',str(checker)],cwd=ROOT,capture_output=True,text=True,timeout=120)
recorded=(K/'observations/payload-attempt01/stdout').read_text()
need(run.returncode==0 and not run.stderr and run.stdout==recorded,'K external checker rerun differs')

# Recheck live data and selected/provider guards after all arithmetic and the
# subprocess; this is sampling, not continuous monitoring.
need(all(p.read_bytes()==before[name] for name,p in paths.items()) and checker.read_bytes()==checker_before,'source/payload changed during audit')
need(inventory(kroots)==before_k and selected(km) and selected(prior) and selected(tm),'selected provider changed during audit')
need(all(record(p)==v for p,v in prior['guards_before'].items()) and all(record(p)==v for p,v in tm['guards_before'].items()),'union guard changed during audit')
for name,records in prior_provider_records.items():
    need(all(record(path)==rec for path,rec in records.items()),'prior provider changed during audit: '+name)
for directory,attempt,module,source_pin,object_pin in producers:
    producer(directory,attempt,module,source_pin,object_pin)

print(json.dumps({'status':'PASS_SOURCE_ARTIFACT_EXTERNAL_NOT_LEAN_REPLAY',
 'K_manifest_sha256':digest(kprep),'K_provider_roots':len(kroots),'K_provider_records':len(before_k),
 'K_selected_files':len(klive),'K_overlap_occurrences':koverlaps,
 'tuple_manifest_sha256':digest(tprep),'tuple_selected_files':len(tm['files']),
 'underlying_selected_files':{n:len(v) for n,v in prior_maps.items()},
 'pairwise_overlap_counts':pairwise,'producer_receipts':prod,
 'rows':len(rows),'copy_slots':len(slots),'raw_bytes':len(raw),'K_bits':total.bit_length(),
 'K_raw_sha256':sha256(raw).hexdigest(),'independent_integer_matches':True,'mutated_row_rejected':True,
 'external_checker_exit':run.returncode,'external_checker_output_sha256':sha256(run.stdout.encode()).hexdigest(),
 'supplement_matches_parent':True,'inputs_and_guards_unchanged':True,
 'scope':'source/artifact and external arithmetic only; no Lean replay, filesystem theorem, or iPRA endpoint'},
 indent=2,sort_keys=True))
