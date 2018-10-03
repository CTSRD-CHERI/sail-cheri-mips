.PHONY: all language clean archs isabelle-lib apply_header mips_sims cheri_sims

INSTALL_DIR ?= .

all: mips_sims cheri_sims

mips_sims:
	$(MAKE) -C mips mips mips_c
cheri_sims:
	$(MAKE) -C cheri cheri cheri_c
	$(MAKE) -C cheri cheri128 cheri128_c

install:
	mkdir -p $(INSTALL_DIR)/bin
	cp -fv mips/mips $(INSTALL_DIR)/bin/sail-mips
	cp -fv mips/mips_c $(INSTALL_DIR)/bin/sail-mips_c
	cp -fv cheri/cheri $(INSTALL_DIR)/bin/sail-cheri
	cp -fv cheri/cheri_c $(INSTALL_DIR)/bin/sail-cheri_c
	cp -fv cheri/cheri128 $(INSTALL_DIR)/bin/sail-cheri128
	cp -fv cheri/cheri128_c $(INSTALL_DIR)/bin/sail-cheri128_c

uninstall:
	rm -f $(INSTALL_DIR)/bin/sail-mips
	rm -f $(INSTALL_DIR)/bin/sail-mips_c
	rm -f $(INSTALL_DIR)/bin/sail-cheri
	rm -f $(INSTALL_DIR)/bin/sail-cheri_c
	rm -f $(INSTALL_DIR)/bin/sail-cheri128
	rm -f $(INSTALL_DIR)/bin/sail-cheri128_c

language:
	$(MAKE) -C language

interpreter:
	$(MAKE) -C src interpreter

archs:
	for arch in arm mips cheri; do\
	  $(MAKE) -C "$$arch" || exit;\
	done

isabelle-lib:
	$(MAKE) -C isabelle-lib

apply_header:
	$(MAKE) clean
	headache -c etc/headache_config -h etc/mips_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/mips_header `ls cheri/*.sail`
	headache -c etc/headache_config -h LICENCE `ls src/Makefile*`
	headache -c etc/headache_config -h LICENCE `ls src/*.ml*`
	headache -c etc/headache_config -h LICENCE `ls src/lem_interp/*.ml`
	headache -c etc/headache_config -h LICENCE `ls src/lem_interp/*.lem`
	$(MAKE) -C arm apply_header

anon_dist:
	headache -c etc/headache_config -h etc/anon_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/anon_header `ls cheri/*.sail`
	headache -c etc/headache_config -h etc/anon_header `ls riscv/*.sail`
	headache -c etc/headache_config -h etc/anon_header `ls riscv/*.ml`
	headache -c etc/headache_config -h etc/anon_header `ls lib/*.ml`
	headache -c etc/headache_config -h etc/anon_header `ls lib/coq/*.v`
	headache -c etc/headache_config -h etc/anon_header `ls src/Makefile*`
	headache -c etc/headache_config -h etc/anon_header `ls src/*.ml*`
	headache -c etc/headache_config -h etc/anon_header `ls src/*.lem`
	headache -c etc/headache_config -h etc/anon_header `ls src/lem_interp/*.ml`
	headache -c etc/headache_config -h etc/anon_header `ls src/lem_interp/*.lem`
	headache -c etc/headache_config -h etc/anon_header `ls arm/*.sail`
	headache -c etc/headache_config -h etc/anon_header `ls snapshots/isabelle/lib/sail/*.thy`
	headache -c etc/headache_config -h etc/anon_header `ls snapshots/isabelle/lib/lem/*.thy`
	headache -c etc/headache_config -h etc/anon_header `ls snapshots/hol4/lem/hol-lib/*.sml`
	rm mips/sim.dts

clean:
	for subdir in src arm ; do\
	  $(MAKE) -C "$$subdir" clean;\
	done
	-rm sail
