TARGET := kill-example

SRC_DIR = $(shell realpath .)
LIBBPF_DIR = $(SRC_DIR)/../libbpf/src/
CFLAGS ?= -I$(LIBBPF_DIR)/root/usr/include/
LDFLAGS ?= -L$(LIBBPF_DIR)

LIBS = -lbpf -lelf

all: $(TARGET) kern.o add_example.o

.PHONY: clean

clean:
	rm -f $(TARGET)
	rm -f kern.o
	rm -f kern.ll

$(TARGET): %: user.c Makefile
	gcc $(CFLAGS) $(LDFLAGS) -o $(TARGET) user.c -Wl,-rpath=$(LIBBPF_DIR) $(LIBS)

kern.o: kern.c
	clang -S \
	    -target bpf \
	    -D __BPF_TRACING__ \
	    $(CFLAGS) \
	    -Wall \
	    -Werror \
	    -O2 -emit-llvm -c -g kern.c
	llc -march=bpf -filetype=obj -o kern.o kern.ll
add_example.o: add_example.c
	clang -S \
            -target bpf \
            -D __BPF_TRACING__ \
            $(CFLAGS) \
            -Wall \
            -Werror \
            -O0 -emit-llvm -c -g add_example.c
	llc -march=bpf -filetype=obj -o add_example.o add_example.ll

