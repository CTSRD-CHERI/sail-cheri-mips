include ../etc/sail.mk

TRACE?=no
ifeq ($(TRACE),yes)
TRACE_SAIL=trace.sail
else
TRACE_SAIL=notrace.sail
endif

MIPS_PRE:=$(TRACE_SAIL) prelude.sail mips_prelude.sail 
MIPS_TLB:=mips_tlb.sail
MIPS_TLB_STUB:=mips_tlb_stub.sail
MIPS_SAILS:=mips_wrappers.sail mips_ast_decl.sail mips_insts.sail mips_ri.sail mips_epilogue.sail
MIPS_MAIN:=main.sail

mips: $(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS) $(MIPS_MAIN)
	$(SAIL) -ocaml -o mips -memo_z3 $(filter %.sail, $^)

mips.c: $(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS) $(MIPS_MAIN) Makefile
	$(SAIL) -O -memo_z3 -c $(filter %.sail, $^) 1> $@

C_WARNINGS=-Wall -Wno-unused-but-set-variable -Wno-unused-label -Wno-unused-function -Wno-maybe-uninitialized
C_OPT=-O2
GCOV_FLAGS=
mips_c: mips.c $(SAIL_LIB_DIR)/sail.h $(SAIL_LIB_DIR)/*.c Makefile
	gcc $(C_OPT) $(C_WARNINGS) $(GCOV_FLAGS) -g -I $(SAIL_LIB_DIR) $< $(SAIL_LIB_DIR)/*.c -lgmp -lz -o $@

# Note that for coverage purposes O1 appears optimal. O0 means lots of obviously dead code but O2 risks reducing granularity too much.
mips_c_gcov: C_OPT=-O1
mips_c_gcov: GCOV_FLAGS=-fprofile-arcs -ftest-coverage
mips_c_gcov: mips_c

gcovr:
	gcovr -r . --html --html-detail -o index.html

sim.dtb: sim.dts
	dtc -O dtb -o $@ -b 0 $<

mips_no_tlb.lem: $(MIPS_PRE) $(MIPS_TLB_STUB) $(MIPS_SAILS)
	$(SAIL) -lem -o mips_no_tlb -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
mips_no_tlb_types.lem: mips_no_tlb.lem

mips.lem: $(MIPS_PRE) $(SAIL_LIB_DIR)/mono_rewrites.sail $(MIPS_TLB) $(MIPS_SAILS)
	$(SAIL) -lem -o mips -auto_mono -mono_rewrites -lem_mwords -lem_lib Mips_extras -undefined_gen -memo_z3 $^
mips_types.lem: mips.lem

mips.v: $(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS)
	$(SAIL) -coq -dcoq_undef_axioms -o mips -coq_lib mips_extras -undefined_gen -memo_z3 $^
mips_types.v: mips.v

MIPS_COQ = mips_types.v mips_extras.v mips.v
#COQ_LIBS = -Q ../../bbv/theories bbv -Q $(SAIL_LIB_DIR)/coq Sail
COQ_LIBS = 

%.vo: %.v
	coqc $(COQ_LIBS) $<
mips.vo: mips_types.vo mips_extras.vo

M%.thy: m%.lem m%_types.lem mips_extras.lem
	lem -isa -outdir . -lib Sail=$(SAIL_DIR)/src/gen_lib -lib Sail=$(SAIL_DIR)/src/lem_interp $^
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' M$*_types.thy

%Script.sml: %.lem %_types.lem mips_extras.lem
	lem -hol -outdir . -lib $(SAIL_LIB_DIR)/hol -i $(SAIL_LIB_DIR)/hol/sail2_prompt_monad.lem -i $(SAIL_LIB_DIR)/hol/sail2_prompt.lem -lib $(SAIL_DIR)/src/gen_lib -lib $(SAIL_DIR)/src/lem_interp $^

%Theory.uo: %Script.sml
	SAIL_LIB_DIR="$(SAIL_LIB_DIR)" Holmake $@

LOC_FILES:=$(MIPS_PRE) $(MIPS_TLB) $(MIPS_SAILS) $(MIPS_MAIN)
include ../etc/loc.mk

clean:
	rm -rf mips Mips.thy mips.lem mips_types.lem _sbuild mips.c mips_c
	rm -f mipsScript.sml mips_typesScript.sml mips_extrasScript.sml
	rm -f mips.v mips_types.v $(MIPS_COQ:%.v=%.vo) $(MIPS_COQ:%.v=%.glob) $(MIPS_COQ:%.v=.%.aux)
	-Holmake cleanAll
