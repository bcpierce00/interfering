all: Makefile.coq 
	$(MAKE) -f Makefile.coq 

Makefile.coq: 
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

test:
	coqc -R . StackSafety -R ../../mit-riscv/riscv-coq/src/riscv riscv -Q ../../mit-riscv/coqutil/src/coqutil coqutil -Q ../../mit-riscv/coq-record-update/src RecordUpdate Gen.v

.PHONY: build clean
