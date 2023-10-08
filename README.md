# Using eBPF (Typical workflow)

- Create a bpf object file, containing at the minimum the following:
  - definition of functions or structs etc, placed in maps at different keys / sections
  - should have atleast one function.
  - defined function's context.
  - can have more structs / functions as needed.
  - compile to get llvm file.
  - compile to get object file, this is the bpf object file.

- Mainfile (in code)
  - open object file
  - check for errors opening (using libbpf)
  - get program using key (name of the compiled program i.e. target)
  - load ebpf object file in kernel
  - attach program to tracepoint (+ check errors)
  - Your logic here!!! Arbitrary
  - Cleanup
    - destroy link (attached above on tracepoint)
	- close the file