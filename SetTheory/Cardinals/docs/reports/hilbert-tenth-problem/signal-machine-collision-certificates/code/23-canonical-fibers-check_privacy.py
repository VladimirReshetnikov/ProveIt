"""Read-only scan for private authoring and tool paths in delivered text.

The final PDF also needs the separate extracted-text and visual QA recorded in
report22-qa.json. This scan deliberately does not claim to parse binary PDFs.
"""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
TOKENS=['/'+'workspace/','/'+'root/','/'+'home/agent/','skill'+':/','file'+':/']

def main():
    examined=0;findings=[]
    for path in sorted(ROOT.rglob('*')):
        if not path.is_file() or path.suffix.lower()=='.pdf':continue
        try:text=path.read_text()
        except UnicodeDecodeError:continue
        examined+=1
        for number,line in enumerate(text.splitlines(),1):
            if any(token in line for token in TOKENS):findings.append({'file':path.relative_to(ROOT).as_posix(),'line':number})
    if findings:raise ValueError('Private authoring path matches: '+json.dumps(findings))
    print(json.dumps({'status':'passed','text_files_scanned':examined,'private_authoring_path_matches':0,'pdf_scan':'separate final extracted-text QA required'},indent=2))

if __name__=='__main__':main()
