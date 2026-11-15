# Builds the development with the standard Coq / Rocq tooling.
#
#   make        -- compile everything
#   make clean  -- remove build products
#
# The makefile generator is `coq_makefile` when it is on the path (Coq 8.x,
# or Rocq with the compatibility binaries) and `rocq makefile` otherwise.
# To choose explicitly:   make GEN="rocq makefile"
COQMAKEFILE := CoqMakefile
GEN ?= $(shell command -v coq_makefile >/dev/null 2>&1 && echo coq_makefile || echo rocq makefile)

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	$(GEN) -f _CoqProject -o $(COQMAKEFILE)

clean:
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) cleanall; fi
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf .$(COQMAKEFILE).d .lia.cache

.PHONY: all clean
