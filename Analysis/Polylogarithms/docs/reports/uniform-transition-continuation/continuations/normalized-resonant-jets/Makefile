.PHONY: pdf check clean
pdf:
	sh build.sh
check:
	python verification/verify.py --part all --output-dir replay
	python verification/verify_extensions.py --output-dir replay
clean:
	rm -f resonant_polylog_transseries.aux resonant_polylog_transseries.log resonant_polylog_transseries.out resonant_polylog_transseries.toc
