CXX ?= c++
CXXFLAGS ?= -O3 -std=c++17 -Wall -Wextra -pedantic
.PHONY: check search lean paper clean
.build/exact_search: src/exact_search.cpp
	mkdir -p .build
	$(CXX) $(CXXFLAGS) $< -o $@
check:
	python3 verify/verify_field.py
	sh tests/test_search.sh
	python3 verify/audit_summary.py results/full_run_summary.json
search: .build/exact_search
	./.build/exact_search 2147483648 experiments/full_data
lean:
	lake build
paper:
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error main.tex && pdflatex -interaction=nonstopmode -halt-on-error main.tex
clean:
	rm -rf .build
