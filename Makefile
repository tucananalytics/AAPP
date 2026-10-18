# Builds the development with the Coq (Rocq) standard tooling.
#   make        -- compile everything
#   make clean  -- remove build products
COQMAKEFILE := CoqMakefile

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean:
	-$(MAKE) -f $(COQMAKEFILE) cleanall 2>/dev/null
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all clean
