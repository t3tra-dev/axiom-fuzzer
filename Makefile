.PHONY: build release test test-timing test-eval rocq rocq-editor check bench bench-external stress-processes clean
# Binaries that are run, measured or evaluated: dune's release profile (no -opaque; the root dune
# file adds -O3, which only a Flambda compiler uses). Only the default context is built, so an
# editor context (dune-workspace.editor) keeps its dev build. Run it under the development switch,
# for example
#   opam exec --switch=5.5.2+flambda -- make release
RELEASE_TARGETS = $(addprefix ./_build/default/,bin/fuzz/main.exe bin/replay/main.exe \
	bin/minimize/main.exe bin/mutate/main.exe bin/reference/main.exe \
	bench/schema/schema_bench.exe benchmarks/replay_bench.exe \
	benchmarks/guidance_bench.exe benchmarks/progress_bench.exe)
build:
	dune build
release:
	dune build --profile release $(RELEASE_TARGETS)
# Three test tiers: runtest (deterministic: searches bounded by caps or with generous wall limits),
# runtest-timing (wall-clock deadlines, signals and process reclamation, one at a time) and
# runtest-eval (every evaluation-only member). `make test` runs the first two.
test:
	dune runtest
	dune build @runtest-timing
test-timing:
	dune build @runtest-timing
test-eval:
	dune build @runtest-eval
rocq:
	dune build @rocq
rocq-editor:
	python3 scripts/rocq-editor.py --build
check:
	dune build @ci
bench: release
	python3 benchmarks/run.py
bench-external:
	bash benchmarks/external.sh
stress-processes: build
	dune build tests/regression/process_chaos.exe
	python3 -B tests/regression/process_chaos.py _build/default/tests/regression/process_chaos.exe --trials 1000 --jobs 8 --kill-supervisor 0.5 --quiet
	python3 -B tests/regression/process_stress.py _build/default/bin/fuzz/main.exe --trials 1000 --jobs 4 --max-seconds 1.5 --quiet
clean:
	dune clean
