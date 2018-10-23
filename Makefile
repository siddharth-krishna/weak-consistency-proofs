civl = boogie -noinfer -typeEncoding:m -useArrayTheory
impls = $(wildcard lib/impls/*.bpl)
targets = $(patsubst lib/impls/%.bpl,%,$(impls))
prelude = $(wildcard lib/prelude/*.bpl)

all: $(targets)

.SECONDEXPANSION:
$(targets): %: $(prelude) lib/adts/$$(lastword $$(subst -, ,$$@)).bpl lib/impls/%.bpl
	@echo Verifying implementation: $@
	@echo ---
	$(civl) $^
	@echo ---
