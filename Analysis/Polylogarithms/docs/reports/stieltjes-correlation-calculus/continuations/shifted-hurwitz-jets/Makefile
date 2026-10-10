.PHONY: pdf exact verify checksums
pdf:
	python code/build.py
exact:
	python code/identity_engine.py --max-total 6
verify:
	python code/verify_numerically.py --dps 50
checksums:
	python code/checksums.py --verify
