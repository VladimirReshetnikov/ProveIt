"""Strict offline I/O, provenance, and fresh-output helpers for Report193."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat

ROOT=Path(__file__).absolute().parent
MANIFEST='PROVENANCE.json'
MAX_FILE_BYTES=4*1024*1024
MAX_TOTAL_BYTES=16*1024*1024
SOURCES=(
 'README.md','certificate_io.py','interval_decimal.py','airy_interval.py',
 'jet_interval.py','real_kernel.py','integrate_core.py','check_exact.py',
 'test_intervals.py','test_guards.py','certificate.py','reproduce.py',
 'fixtures/README.md','fixtures/core_reference.json',
 'fixtures/panels_reference.json','fixtures/coefficient_reference.json',
)
# These digests identify the regression fixtures; results are recomputed, never trusted as proof.
FIXTURE_SHA256={'coefficient_reference.json': '79a4fa072a4dcecbc003e8f1a22ba354def01ee3e5710ec407f7c953e52fc6a7', 'core_reference.json': '4e2c38e9ba7577cbad3bd87d7e5a6c510dd596f7f1f509e05a3030d7511a04ce', 'panels_reference.json': '1729842c6b771d391075e68a1db1bcd48caf90ce70d1b222aedf92b01c63ca11'}

def need(condition,message):
 if not condition:raise ValueError(message)

def canonical(value):
 return (json.dumps(value,sort_keys=True,indent=2,ensure_ascii=True,allow_nan=False)+'\n').encode('utf-8')

def sha(data):return hashlib.sha256(data).hexdigest()

def unique_object(pairs):
 result={}
 for key,value in pairs:
  need(key not in result,'Duplicate JSON key: '+key);result[key]=value
 return result

def invalid_constant(value):raise ValueError('Non-finite JSON constant: '+value)

def noninteger_number(value):raise ValueError('Noninteger JSON number is forbidden: '+value)

def load_json(data):
 return json.loads(data,object_pairs_hook=unique_object,parse_constant=invalid_constant,parse_float=noninteger_number)

def safe_name(name):
 need(type(name) is str and bool(name),'Invalid package path')
 need(not any(ord(c)<32 or ord(c)==127 for c in name) and '\\' not in name and ':' not in name,'Unsafe package path')
 path=PurePosixPath(name)
 need(not path.is_absolute() and path.parts and all(p not in ('.','..') for p in path.parts)
      and path.as_posix()==name,'Unsafe package path')
 need(not any(p in ('__pycache__','.cache','.DS_Store') or p.endswith(('.pyc','.pyo')) for p in path.parts),'Cache path is forbidden')
 return path

def check_directory(path):
 path=Path(path).absolute()
 need('..' not in path.parts,'Directory traversal is forbidden')
 for item in (*reversed(path.parents),path):
  need(stat.S_ISDIR(item.lstat().st_mode),'Missing, linked, or non-directory path: '+str(item))
 return path

def read_regular(path,limit=MAX_FILE_BYTES):
 path=Path(path).absolute();check_directory(path.parent)
 initial=path.lstat()
 need(stat.S_ISREG(initial.st_mode) and initial.st_size<=limit,'Not a bounded regular file: '+str(path))
 fd=os.open(path,os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_NONBLOCK',0))
 with os.fdopen(fd,'rb') as stream:
  opened=os.fstat(stream.fileno())
  need(stat.S_ISREG(opened.st_mode) and opened.st_size<=limit,'Invalid opened file')
  need((initial.st_dev,initial.st_ino)==(opened.st_dev,opened.st_ino),'File changed while opening')
  data=stream.read(limit+1)
  need(len(data)<=limit and len(data)==opened.st_size,'File size changed while reading')
 return data

def checked_output(output,source=ROOT):
 output=Path(output).absolute();source=check_directory(source)
 need('..' not in output.parts,'Output traversal is forbidden')
 check_directory(output.parent)
 need(not os.path.lexists(output),'Refusing existing output: '+str(output))
 need(not output.resolve().is_relative_to(source.resolve()),'Output must be outside source directory')
 return output

def write_new(path,data):
 need(type(data) is bytes,'Output must be bytes')
 path=Path(path).absolute();check_directory(path.parent)
 with path.open('xb') as stream:stream.write(data)

def scan(root):
 root=check_directory(root);files={};directories=set()
 def walk(directory):
  with os.scandir(directory) as listing:entries=sorted(listing,key=lambda e:e.name)
  for entry in entries:
   path=Path(entry.path);name=path.relative_to(root).as_posix();safe_name(name)
   info=entry.stat(follow_symlinks=False)
   if stat.S_ISDIR(info.st_mode):directories.add(name);walk(path)
   elif stat.S_ISREG(info.st_mode):
    need(info.st_size<=MAX_FILE_BYTES,'Source too large');files[name]=path
   else:raise ValueError('Nonregular source entry: '+name)
 walk(root)
 return files,directories

def snapshot(root=ROOT):
 files,directories=scan(root)
 expected=set(SOURCES)|{MANIFEST}
 need(len(SOURCES)==len(set(SOURCES)),'Duplicate source allowlist entry')
 need(set(files)==expected,'Closed source inventory mismatch')
 need(directories=={'fixtures'},'Unexpected or empty source directory')
 result={}
 for name,path in sorted(files.items()):
  data=read_regular(path);result[name]={'bytes':len(data),'sha256':sha(data)}
 need(sum(row['bytes'] for row in result.values())<=MAX_TOTAL_BYTES,'Source exceeds aggregate limit')
 return result

def verify_source(root=ROOT):
 found=snapshot(root)
 raw=read_regular(Path(root)/MANIFEST,65536);doc=load_json(raw)
 need(type(doc) is dict and set(doc)=={'schema','report','algorithm','files'},'Provenance schema mismatch')
 need(doc['schema']=='report193-code-v1' and type(doc['report']) is int and doc['report']==193
      and doc['algorithm']=='sha256','Provenance identity mismatch')
 need(type(doc['files']) is dict and set(doc['files'])==set(SOURCES),'Provenance inventory mismatch')
 for name,row in doc['files'].items():
  safe_name(name)
  need(type(row) is dict and set(row)=={'bytes','sha256'},'Provenance row schema mismatch')
  need(type(row['bytes']) is int and 0<=row['bytes']<=MAX_FILE_BYTES,'Invalid provenance size')
  need(type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}',row['sha256']),'Invalid provenance hash')
 need({k:v for k,v in found.items() if k!=MANIFEST}==doc['files'],'Source bytes differ from provenance')
 need(canonical(doc)==raw,'Provenance must use canonical JSON')
 return found

def fixture(name,root=ROOT):
 need(name in FIXTURE_SHA256,'Fixture is not allowlisted')
 raw=read_regular(Path(root)/'fixtures'/name)
 need(sha(raw)==FIXTURE_SHA256[name],'Fixture checksum mismatch')
 doc=load_json(raw);need(canonical(doc)==raw,'Noncanonical fixture')
 return doc
