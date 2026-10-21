from pathlib import Path
import hashlib,json,subprocess,sys,time
P=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
g=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_domrho8_lean.py';c=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/lean217/dominated_rho8_full_certificate.json';s=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before={str(p):h(p) for p in (g,c,s)}
out=P/'regenerated.lean';assert not out.exists();cmd=[sys.executable,'-B',str(g),str(c),str(out)];t=time.monotonic();r=subprocess.run(cmd,capture_output=True,timeout=30)
(P/'regeneration.stdout').write_bytes(r.stdout);(P/'regeneration.stderr').write_bytes(r.stderr)
after={p:h(Path(p)) for p in before};assert r.returncode==0 and before==after and out.read_bytes()==s.read_bytes()
receipt={'status':'PASS','command':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,'before':before,'after':after,'generated_exact_current_source':True,'generated_sha256':h(out),'stdout_sha256':h(P/'regeneration.stdout'),'stderr_sha256':h(P/'regeneration.stderr'),'script_sha256':h(Path(__file__)),'scope':'Generator reproduction on a disposable output only; no Lean compiler.'};(P/'regeneration.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
