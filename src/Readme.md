Dependencies:
coq >= 8.12.1 (possibly lower)
coq-quickchick
coqutil, coq-recordupdate, and riscv-coq should be present and built, update their paths
in \_CoqProject

Properties are in Properties/..., with SubroutineSimpl.v being the main one.
Testing equivalents are in Testing/, and ``make'' will ultimately build up to
Testing/TestProperties.v. Comment and uncomment the tests to run them.
Core/ contains the machine/policy models.
