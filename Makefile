civl = boogie -noinfer -typeEncoding:m -useArrayTheory
adts = $(patsubst lib/adts/%.bpl,%,$(wildcard lib/adts/*.bpl))
impls = $(patsubst lib/impls/%,%,$(wildcard lib/impls/*))
prelude = $(wildcard lib/prelude/*.bpl)

.PHONY: all checks prelude $(adts) $(impls)

all: prelude $(adts) $(impls)

prelude:
	@echo Checking prelude
	@echo ---
	@boogie lib/prelude/invocations.bpl
	@echo ---
	@boogie lib/prelude/*.bpl
	@echo ---

$(adts): %: lib/adts/%.bpl
	@echo Checking ADT: $@
	@echo ---
	@boogie lib/prelude/*.bpl $<
	@echo ---

.SECONDEXPANSION:
$(impls): %: $(prelude) lib/adts/$$(lastword $$(subst -, ,$$@)).bpl $$(wildcard lib/impls/$$@/*.bpl)
	@echo Verifying implementation: $@
	@echo ---
	@$(civl) $^
	@echo ---
