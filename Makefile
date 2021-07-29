.PHONY: all language clean archs isabelle-lib apply_header mips_sims cheri_sims

INSTALL_DIR ?= .

all: mips_sims cheri_sims lem_defs

mips_sims:
	$(MAKE) -C mips mips mips_c
cheri_sims:
	$(MAKE) -C cheri cheri cheri_c cheri128 cheri128_c
lem_defs:
	$(MAKE) -C cheri cheri.lem cheri128.lem


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

apply_header:
	$(MAKE) clean
	headache -c etc/headache_config -h LICENCE `ls mips/*.sail`
	headache -c etc/headache_config -h LICENCE `ls cheri/*.sail`

anon_dist:
	headache -c etc/headache_config -h etc/anon_header `ls mips/*.sail`
	headache -c etc/headache_config -h etc/anon_header `ls cheri/*.sail`
	rm mips/sim.dts

clean:
	for subdir in mips cheri; do\
	  $(MAKE) -C "$$subdir" clean;\
	done

