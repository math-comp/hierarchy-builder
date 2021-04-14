config: log.compat.elpi

log.compat.elpi: log.compat.legacy.elpi log.compat.current.elpi
ifeq "$(COQVV)" "8.11"
	echo '#line 0 "log.compat.legacy.elpi"' > log.compat.elpi
	cat log.compat.legacy.elpi >> log.compat.elpi
else
ifeq "$(COQVV)" "8.12"
	echo '#line 0 "log.compat.legacy.elpi"' > log.compat.elpi
	cat log.compat.legacy.elpi >> log.compat.elpi
else
	echo '#line 0 "log.compat.current.elpi"' > log.compat.elpi
	cat log.compat.current.elpi >> log.compat.elpi
endif
endif

build:

install:

clean:

distclean:

test-suite: