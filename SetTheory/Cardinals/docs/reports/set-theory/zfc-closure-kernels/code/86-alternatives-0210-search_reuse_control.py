import pathlib,sys,os,importlib.util
root=pathlib.Path(__file__).resolve().parent
os.environ['ZFC246_BASE']=str(root/'recovered/63')
os.environ['ZFC246_TABLE']=str(root/'reuse_control8.tm')
spec=importlib.util.spec_from_file_location('f',root/'recovered/64/experiments/decoder/fold_search246.py')
f=importlib.util.module_from_spec(spec);spec.loader.exec_module(f)
f.ROOT=root/'reuse_control_folds';f.ROOT.mkdir(exist_ok=True)
f.main()
