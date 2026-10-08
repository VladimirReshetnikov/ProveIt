import json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
from portkh.complexes import connected_singular_pair,analyze
ROOT=Path(__file__).resolve().parents[1]
class CLI(unittest.TestCase):
    def invoke(self,*args,text=None):
        env=dict(os.environ);env['PYTHONPATH']=str(ROOT/'src')
        return subprocess.run([sys.executable,'-m','portkh',*args],input=text,
                              capture_output=True,text=True,env=env,timeout=10)
    def test_analyze_stdin(self):
        c=connected_singular_pair(40)
        result=self.invoke('analyze','-',text=json.dumps(c.to_dict()))
        self.assertEqual(result.returncode,0,result.stderr)
        self.assertEqual(json.loads(result.stdout)['homology_dimension'],2)
    def test_certificate_replay_and_tamper(self):
        c=connected_singular_pair(4)
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder)/'input.json';q=Path(folder)/'certificate.json'
            p.write_text(json.dumps(c.to_dict()));ans=analyze(c);q.write_text(json.dumps(ans))
            self.assertEqual(self.invoke('verify',str(p),str(q)).returncode,0)
            ans['homology_dimension']=0;q.write_text(json.dumps(ans))
            self.assertEqual(self.invoke('verify',str(p),str(q)).returncode,2)
    def test_minimize_and_example(self):
        ex=self.invoke('example','4','--kind','connected-singular')
        self.assertEqual(ex.returncode,0,ex.stderr)
        mi=self.invoke('minimize','-',text=ex.stdout)
        self.assertEqual(mi.returncode,0,mi.stderr)
        an=self.invoke('analyze','-',text=mi.stdout)
        self.assertEqual(json.loads(an.stdout)['homology_dimension'],2)
    def test_bad_json_and_negative_length(self):
        for text in ('[]','null','not json','{"format":"bad"}'):
            result=self.invoke('analyze','-',text=text)
            self.assertEqual(result.returncode,2)
            self.assertNotIn('Traceback',result.stderr)
        self.assertEqual(self.invoke('example','-1').returncode,2)

class RestrictedCLI(unittest.TestCase):
    invoke = CLI.invoke
    def test_language_replay(self):
        from portkh.complexes import coupled_pair
        from portkh.languages import fixed_weight,analyze_restricted
        c=coupled_pair(7,'invertible');language=fixed_weight(7,3)
        with tempfile.TemporaryDirectory() as folder:
            p=Path(folder)/'input.json';q=Path(folder)/'languages.json';r=Path(folder)/'cert.json'
            p.write_text(json.dumps(c.to_dict()));q.write_text(json.dumps([language.to_dict()]))
            r.write_text(json.dumps(analyze_restricted(c,(language,))))
            result=self.invoke('analyze',str(p),'--languages',str(q))
            self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(json.loads(result.stdout)['homology_dimension'],2)
            self.assertEqual(self.invoke('verify',str(p),str(r),'--languages',str(q)).returncode,0)
