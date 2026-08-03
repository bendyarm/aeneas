# Regenerate the *generated* ACL2 books from the Rust sources, and certify
# the whole directory. Config via environment:
#   AENEAS   path to the aeneas binary        (default ../../bin/aeneas)
#   CHARON   path to the charon binary        (default ../../charon/bin/charon)
#   ACL2     path to the acl2 image           (for cert.pl)
#   CERT_PL  path to books/build/cert.pl
#   SRC      Rust sources dir                 (default ../src)
#   LLBC     scratch dir for .llbc            (default ../llbc)

AENEAS  ?= ../../bin/aeneas
CHARON  ?= ../../charon/bin/charon
SRC     ?= ../src
LLBC    ?= ../llbc
CERT_PL ?= cert.pl
AENEAS_FLAGS ?= -backend acl2 -use-fuel -loops-to-rec

# crate-name -> source stem (extraction crate name sets the ACL2 prefix)
GEN = demo loops no_nested_borrows

.PHONY: regen verify clean
# Regenerate the golden generated books. TEA uses distinct crate names so
# its functions don't clash with the Kestrel spec (rust_tea, rust_tea_arr).
regen:
	@mkdir -p $(LLBC)
	@for f in $(GEN); do \
	  echo "== $$f"; \
	  $(CHARON) rustc --dest-file $(LLBC)/$$f.llbc --preset=aeneas -- \
	    $(SRC)/$$f.rs --crate-name=$$f --crate-type=rlib \
	    --allow=unused --allow=non_snake_case >/dev/null 2>&1; \
	  $(AENEAS) $(AENEAS_FLAGS) -dest . $(LLBC)/$$f.llbc || true; \
	done
	@$(CHARON) rustc --dest-file $(LLBC)/rust_tea.llbc --preset=aeneas -- \
	  $(SRC)/tea.rs --crate-name=rust_tea --crate-type=rlib \
	  --allow=unused --allow=non_snake_case >/dev/null 2>&1
	@$(AENEAS) $(AENEAS_FLAGS) -dest . $(LLBC)/rust_tea.llbc || true
	@$(CHARON) rustc --dest-file $(LLBC)/rust_tea_arr.llbc --preset=aeneas -- \
	  $(SRC)/tea_arr.rs --crate-name=rust_tea_arr --crate-type=rlib \
	  --allow=unused --allow=non_snake_case >/dev/null 2>&1
	@$(AENEAS) $(AENEAS_FLAGS) -dest . $(LLBC)/rust_tea_arr.llbc || true
	@# Vec needs --monomorphize (resolves the SliceIndex trait plumbing)
	@$(CHARON) rustc --dest-file $(LLBC)/vec_demo.llbc --preset=aeneas \
	  --monomorphize -- $(SRC)/vec_demo.rs --crate-name=vec_demo \
	  --crate-type=rlib --allow=unused --allow=non_snake_case >/dev/null 2>&1
	@$(AENEAS) $(AENEAS_FLAGS) -dest . $(LLBC)/vec_demo.llbc || true

# Certify every book in the directory (generated + handwritten).
verify:
	$(CERT_PL) -j $(shell nproc) \
	  rust-primitives demo loops no_nested_borrows proofs \
	  rust_tea tea-bridges tea-equiv tea-vectors \
	  rust_tea_arr tea_arr-vectors tea-arr-equiv \
	  vec_demo vec_demo-proofs

clean:
	rm -f *.cert *.cert.out *.fasl *.port Makefile-tmp
