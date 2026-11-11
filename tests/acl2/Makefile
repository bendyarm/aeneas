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

# The generated books: crate-name:source-stem[:rustc-flag].  The crate name
# sets the ACL2 prefix (TEA uses rust_tea / rust_tea_arr so its functions do
# not clash with the Kestrel spec).  Every crate goes through the same
# pipeline: stock charon with --preset=aeneas, no --monomorphize (and, for
# std_glue_probe, the --include flags of STD_GLUE).
#
#   demo loops no_nested_borrows     the upstream aeneas test crates
#   rust_tea rust_tea_arr            TEA, scalar and array forms
#   vec_demo vec_sum                 Vec
#   aes_probe                        S-box lookup (byte-as-usize cast), in-place
#                                    state xor, rotate_left, functional round,
#                                    xtime and GF(2^8) multiply
#   rev_range                        `for i in (a..b).rev()` (the upstream
#                                    memshift32 shape)
#   range_both                       Range<usize> and Range<i32> in one crate
#   iterators_scalar range_for       `for i in 0..n`
#   aes_fixslice_core                vendored RustCrypto AES fixslice round core
#   aes_fixslice_encrypt             full fixsliced AES-128; shift_rows_* and
#                                    add_round_key are upstream iter_mut()/zip()
#                                    text.  --edition=2021 puts TryInto in the
#                                    prelude for the key schedule's
#                                    slice.try_into() reads
#   cast_probe loop_break subslice_probe lebytes_probe itermut_probe
#   generics_probe traits_probe      regression probes for individual
#                                    constructs, each (but cast_probe) with a
#                                    known-answer proofs book.  traits_probe:
#                                    trait-generic code and closures, printed
#                                    once per trait instance
#   std_glue_probe                   Option::map and friends, the blanket
#                                    Into, == on references: std's own source
#                                    (STD_GLUE below), printed the same way
CRATES = demo:demo loops:loops no_nested_borrows:no_nested_borrows \
  rust_tea:tea rust_tea_arr:tea_arr \
  vec_demo:vec_demo vec_sum:vec_sum \
  aes_probe:aes_probe rev_range:rev_range range_both:range_both \
  iterators_scalar:iterators-scalar range_for:range_for \
  aes_fixslice_core:aes_fixslice_core \
  aes_fixslice_encrypt:aes_fixslice_encrypt:--edition=2021 \
  cast_probe:cast_probe loop_break:loop_break subslice_probe:subslice_probe \
  lebytes_probe:lebytes_probe:--edition=2021 \
  itermut_probe:itermut_probe:--edition=2021 \
  generics_probe:generics_probe traits_probe:traits_probe \
  std_glue_probe:std_glue_probe

# Charon keeps the functions of other crates opaque unless asked.  For
# std_glue_probe these std functions are extracted from their own source, and
# the backend prints them like the crate's own (tests/src/std_glue_probe.rs).
STD_GLUE = --include core::option::_::map --include core::option::_::and_then \
  --include core::option::_::map_or --include core::option::_::unwrap_or_else \
  --include core::option::_::unwrap_or --include core::option::_::is_some \
  --include core::option::_::ok_or --include core::result::_::map \
  --include core::convert::{core::convert::Into<_,_>}::into \
  --include core::convert::num::_::from --include core::cmp::impls::_::eq

.PHONY: regen verify clean
# Regenerate the golden generated books.
regen:
	@mkdir -p $(LLBC)
	@for c in $(CRATES); do \
	  name=$${c%%:*}; rest=$${c#*:}; src=$${rest%%:*}; \
	  flag=; case $$rest in *:*) flag=$${rest#*:};; esac; \
	  extra=; case $$name in std_glue_probe) extra="$(STD_GLUE)";; esac; \
	  echo "== $$name"; \
	  rm -f $(LLBC)/$$name.llbc; \
	  $(CHARON) rustc --dest-file $(LLBC)/$$name.llbc --preset=aeneas $$extra -- $$flag \
	    $(SRC)/$$src.rs --crate-name=$$name --crate-type=rlib \
	    --allow=unused --allow=non_snake_case >/dev/null 2>&1 \
	    || echo "charon failed on $$name"; \
	  $(AENEAS) $(AENEAS_FLAGS) -dest . $(LLBC)/$$name.llbc || true; \
	done

# Certify every book in the directory (generated + handwritten).  The GL
# bit-blasting books need several GB each: on machines with less than ~12 GB
# use `make verify JOBS=1` (with more parallelism they are killed silently).
JOBS ?= $(shell nproc)
verify:
	$(CERT_PL) -j $(JOBS) \
	  rust-primitives demo loops no_nested_borrows proofs \
	  rust_tea tea-bridges tea-equiv tea-vectors \
	  rust_tea_arr tea_arr-vectors tea-arr-equiv \
	  vec_demo vec_demo-proofs vec_sum vec_sum-proofs \
	  aes_probe aes_probe-proofs \
	  iterators_scalar range_for range_for-proofs range_both range_both-proofs rev_range rev_range-proofs \
	  aes_fixslice_core aes_fixslice_core-proofs \
	  aes_fixslice_encrypt aes_fixslice_encrypt-proofs \
	  aes_fixslice_bijection \
	  aes_fixslice_correspondence aes_fixslice_subbytes \
	  aes_fixslice_mixcolumns aes_fixslice_addroundkey aes_fixslice_round \
	  aes_fixslice_shiftrows aes_fixslice_rounds aes_fixslice_keyschedule \
	  aes_fixslice_keycore aes_fixslice_keychain aes_fixslice_keyops aes_fixslice_keyround aes_fixslice_keycrux aes_fixslice_keystep aes_fixslice_keyframe aes_fixslice_keyexpand aes_fixslice_keyfold aes_fixslice_keysched aes_fixslice_keydecomp aes_fixslice_keyasm aes_fixslice_keyread aes_fixslice_keybridge aes_fixslice_keymain aes_fixslice_cipher aes_fixslice_cipherops aes_fixslice_maskalg aes_fixslice_windows aes_fixslice_ladder aes_fixslice_final \
	  cast_probe loop_break loop_break-proofs subslice_probe subslice_probe-proofs \
	  lebytes_probe lebytes_probe-proofs itermut_probe itermut_probe-proofs \
	  generics_probe generics_probe-proofs traits_probe traits_probe-proofs \
	  std_glue_probe std_glue_probe-proofs \
	  aes_fixslice_invops_defs aes_fixslice_invops aes_fixslice_invops2 aes_fixslice_invops3 \
	  aes_fixslice_decoptypes aes_fixslice_decipherops aes_fixslice_decmask aes_fixslice_decipher \
	  aes_fixslice_decladder aes_fixslice_decfinal

clean:
	rm -f *.cert *.cert.out *.fasl *.port Makefile-tmp
