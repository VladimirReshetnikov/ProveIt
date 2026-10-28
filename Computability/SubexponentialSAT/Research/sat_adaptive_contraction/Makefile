.PHONY: report check benchmark verify
report:
	python3 build_report.py
check:
	python3 run_checks.py
benchmark:
	python3 code/benchmark_kernel.py --repeats 5 --output results/benchmark_rerun.json
verify:
	python3 verify_manifest.py
