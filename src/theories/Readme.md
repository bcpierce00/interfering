Dependencies:
coq >= 8.12.1 (possibly lower)
coq-quickchick (testing on 1.6.4)
zarith (testing on 1.12)
coqutil, coq-recordupdate, and riscv-coq should be present and built, update their paths
in \_CoqProject or use included submodules (must be built separately, pinned
commits work with Coq 8.11 and 8.12, more recent versions require other commits
and propagation of API changes throughout the code)

Core/ contains the abstract machine and policy models, as well as the RISCV
instantiations with different policies.

Properties/ contains Coq definitions corresponding to the different Properties:
- Trace.v and ObsTrace.v define the trace model and observation model

- TraceProperties.v defines generic trace properties for integrity and confidentiality,
  both stepwise and observational.

- SubroutineSimple.v defines the core stack safety property, first giving the stepwise
  properties explicitly in a style similar to the paper, then the equivalent properties
  using the generic trace properties from TraceProperties.v, and finally observational
  properties..

  ContextUpdate => Line 126

  Definition 2  => Line 179

  Definition 9  => Line 228

  Definition 11 => Line 256

  Definition 13 => Line 264

  Definition 10 => Line 274

- CalleeSave.v defines stack safety with callee-save registers.
  
  ContextUpdate => Line 62
  
  Definition 20 => Line 123 & Line 130

- SubroutineShare.v defines the version enhanced with argument passing on the stack.
  Note that a preliminary treatment of address-taken locals is present; we discuss this briefly
  in the submission, but find it uninteresting in a model that lacks a heap.

  ContextUpdate => 82

  Definition 23 => Line 154 & Line 159

- Coroutine.v defines the coroutine version. Unlike in the paper, passing on the stack is included.

  ContextUpdate => Line 107

  Definition 16 => Line 199 & Line 222

  Definition 17 => Line 213 & Line 247

Testing/ contains the test system, with generators for different machines and the final test run
via extraction in TestProperties.v
