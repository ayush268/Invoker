.PHONY: clean build ubuntu-deps test libbpf

ubuntu-deps:
	sudo apt update
	sudo apt install -y build-essential git make gcc clang llvm libelf-dev gcc-multilib
	$(MAKE) modules

modules:
	git submodule update --init

libbpf:
	$(MAKE) --directory=libbpf/src all
	DESTDIR=root $(MAKE) --directory=libbpf/src install_headers

build: libbpf
	$(MAKE) --directory=src

clean:
	$(MAKE) --directory=src clean
	$(MAKE) --directory=libbpf/src clean

test:
	./test/test.sh

.DEFAULT_GOAL := build
