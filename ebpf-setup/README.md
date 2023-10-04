# ebpf-setup

This sub project is for setting up ebpf on your machine/docker and showing the feasibility + viability of eBPF.

Furthermore, the project shows how to create and run a simple eBPF program.

## Minimum requirements

To run this example, the following software is required.

- **Linux kernel v4.19+**
- **LLVM 10+**
- libelf-dev (For Ubuntu, Installed via *make deps*)
- gcc-multilib (For Ubuntu, Installed via *make deps*)

## Installation

To install, first clone the repository.

```
git clone https://github.com/ayush268/Invoker
```

Install dependencies needed to compile *ebpf-setup*.

```
make ubuntu-deps
```

Compile the example program.

```
make
```

## Usage

Run the example program. Super user privileges are required to load the program into the kernel.

```
sudo ./src/kill-example
```

## Test

To test *kill-example*, run `make test`.
This will load the eBPF program, start a looping process and kill it. It will verify that the eBPF program was invoked when kill was called.

```
➜  ebpf-setup git:(main) ✗ make test
./test/test.sh
-- Loading eBPF program.
-- Starting test process to kill.
-- PID of test process is 49852.
-- Killed. Waiting for eBPF program to terminate ..
[ OK ] -- eBPF program ran as expected.
```

## Contributing
Pull requests are welcome. For major changes, please open an issue first to discuss what you would like to change.

Please make sure to update tests as appropriate.