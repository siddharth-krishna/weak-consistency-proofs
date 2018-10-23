civl = boogie -noinfer -typeEncoding:m -useArrayTheory
adts = $(patsubst lib/adts/%.bpl,%,$(wildcard lib/adts/*.bpl))
impls = $(patsubst lib/impls/%.bpl,%,$(wildcard lib/impls/*.bpl))
prelude = $(wildcard lib/prelude/*.bpl)

.PHONY: all checks prelude-checks adt-checks $(adts)

all: checks $(impls)

checks: prelude-checks adt-checks

prelude-checks:
	@echo Checking prelude
	@echo ---
	@boogie lib/prelude/invocations.bpl
	@echo ---
	@boogie lib/prelude/*.bpl
	@echo ---

adt-checks: $(adts)

$(adts): %: lib/adts/%.bpl
	@echo Checking ADT: $@
	@echo ---
	boogie lib/prelude/*.bpl $<
	@echo ---

.SECONDEXPANSION:
$(impls): %: $(prelude) lib/adts/$$(lastword $$(subst -, ,$$@)).bpl lib/impls/%.bpl
	@echo Verifying implementation: $@
	@echo ---
	$(civl) $^
	@echo ---
