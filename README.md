# MoreC

This directory contains sources for the Coq development corresponding to
the ITP24 paper "Defining and Preserving More C Behaviors: Verified Compilation Using a Concrete Memory Model"

These files are known to compile under the following configuration:
- Coq 8.18.0 compiled with OCaml 4.14.1  
- coq-equations1.3 [see https://github.com/mattam82/Coq-Equations for installation instructions if necessary]

Just type 'make'...

Summary of files, with corresponding paper sections:

- Mem.v           -- interface of the memory model                   (section 4)
- RTL.v           -- source language                                 (section 5.1)
- Mach.v          -- target machine and RTS                          (section 5.2,5.4)
- Compiler.v      -- compilation                                     (section 5.3)
- SourceMem.v     -- instantiation of the memory model               (section 5.5)
- Separation.v    -- separation logic for Mach memory                (section 5.6; modified from CompCert)
- Matching.v      -- matching relations for refinement proof         (section 5.6)
- Sim.v           -- the refinement proof                            (section 5.6)
- TopLevel.v      -- the top-level theorem                           (section 5.6)

- Smallstep.v   -- definitions and lemmas for smallstep semantics (modified from CompCert)
- Behaviors.v   -- overall program behaviors (modified from CompCert)
- Zbits.v       -- Z arithmetic lemmas (from CompCert)        
- Integers.v    -- machine integers (from CompCert)
- Errors.v      -- an error monad (from CompCert)
- Maps.v        -- efficient maps (from CompCert)
- Coqlib.v      -- helpful utiltiies (from CompCert)

