# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: default linux linux-on-macos macos clean

# --------------------------------------------------------------------
default:
	@echo "make [linux|macos]"

linux:
	scripts/build-linux.sh

linux-on-macos:
	docker run -t -i -v "$$PWD:/home/ci/package" easycryptpa/ec-build-box \
	  sh -c '( set -ex; cp -a package package.dev && make -C package.dev linux && cp -a package.dev/_build package )'

macos:
	scripts/build-macos.sh

clean:
	rm -rf _build
